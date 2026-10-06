# tools/scripts/daemon_ipc.py
#
# Transport layer shared by the warm retrieval daemons (embed_daemon.py,
# rerank_daemon.py) and their clients (embed_text.py, rerank_query.py).
#
# Why this module exists: the daemons used to call socket.AF_UNIX directly, which
# CPython does NOT expose on Windows (cpython#77589 / bpo-33408) even though the OS
# has supported AF_UNIX since Windows 10 1803. That raised AttributeError — not
# OSError — so it escaped the clients' `except OSError` fallback and killed the whole
# process instead of degrading to their inline model load. Semantic retrieval was
# therefore dead on Windows regardless of whether the model weights were present.
#
# Two transports, one endpoint concept:
#   POSIX   — an AF_UNIX stream socket bound at the endpoint path. The socket file's
#             permissions are the access control, and a second bind fails EADDRINUSE,
#             which is what stops a redundant daemon.
#   Windows — a LOOPBACK TCP socket on an ephemeral port; the daemon publishes
#             "<port>\n<token>" into the endpoint path and clients read it back.
#
# The loopback transport has to REBUILD two properties the unix socket got for free:
#   * Access control. Any local process can reach 127.0.0.1, so the daemon mints a
#     random token, publishes it in the (user-readable) endpoint file, and refuses any
#     peer that cannot present it. That also stops a recycled ephemeral port belonging
#     to an unrelated service from being mistaken for our daemon.
#   * Single ownership. bind(port 0) ALWAYS succeeds, so it cannot refuse a redundant
#     daemon the way an AF_UNIX bind does. Publication is therefore an exclusive
#     create: whoever creates the endpoint file owns it, and the loser exits instead of
#     overwriting the winner. A daemon also only ever removes an endpoint file that
#     still names its own port, so an exiting straggler cannot delete a live daemon's
#     endpoint and strand every later client.
#
# Everything ABOVE this layer (the length-prefixed binary protocol, the model, the
# pooling, the query prefix, the normalization) is byte-identical on both platforms,
# so daemon and inline vectors live in the same space as the precomputed corpus
# embeddings on every OS.
#
# Contract: every function here raises OSError — never AttributeError, UnicodeError or
# ValueError — when no live daemon is reachable, which is what the clients'
# fall-back-to-inline path expects. Endpoint files are read as strict ASCII and any
# malformed content is reported as ConnectionRefusedError so it is cleaned up like a
# stale one.
import hashlib
import os
import secrets
import socket
import subprocess
import sys
import tempfile

# CPython exposes AF_UNIX on POSIX only; on Windows we take the loopback-TCP path.
HAS_UNIX = hasattr(socket, "AF_UNIX")

TOKEN_LEN = 32  # hex chars; fixed width so the daemon reads it without over-reading
DEFAULT_CONN_TIMEOUT = 180.0
HANDSHAKE_TIMEOUT = 10.0  # a token exchange takes microseconds; only a stall takes longer


class DaemonAlreadyRunning(Exception):
    """Another daemon owns this endpoint; this process should exit without serving."""


def endpoint(prefix, key):
    """Per-(repo, model) endpoint path in the temp dir, so distinct checkouts and
    distinct models never share a daemon. `.sock` is the bound AF_UNIX socket on
    POSIX; `.port` is the published loopback port file on Windows."""
    h = hashlib.sha1(key.encode()).hexdigest()[:12]
    return os.path.join(tempfile.gettempdir(),
                        f"causalean-{prefix}-{h}.{'sock' if HAS_UNIX else 'port'}")


def _recvn(conn, n):
    buf = bytearray()
    while len(buf) < n:
        chunk = conn.recv(n - len(buf))
        if not chunk:
            return None
        buf += chunk
    return bytes(buf)


def _read_endpoint(path):
    """Parse a published "<port>\\n<token>" file.

    Every malformed shape — non-ASCII bytes, a Unicode digit like '²' that str.isdigit
    accepts but int() rejects, a truncated file — is converted to ConnectionRefusedError
    so that callers see one OSError subclass and clean the endpoint up."""
    try:
        with open(path, "r", encoding="ascii", errors="strict") as fh:
            raw = fh.read(128)  # bounded: a pathological file must not raise MemoryError
    except ValueError as e:  # UnicodeDecodeError is a ValueError, NOT an OSError
        raise ConnectionRefusedError(f"unreadable daemon endpoint {path}: {e}") from e
    parts = raw.split("\n")
    try:
        port = int(parts[0].strip())
    except (ValueError, IndexError) as e:
        raise ConnectionRefusedError(f"malformed daemon endpoint {path}: {e}") from e
    token = parts[1].strip() if len(parts) > 1 else ""
    if not 0 < port < 65536 or len(token) != TOKEN_LEN:
        raise ConnectionRefusedError(f"malformed daemon endpoint {path}")
    return port, token


def connect(path, timeout=DEFAULT_CONN_TIMEOUT):
    """Connect to the daemon owning `path`. Raises OSError if none is live."""
    if HAS_UNIX:
        c = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        c.settimeout(timeout)
        try:
            c.connect(path)
        except OSError:
            c.close()  # do not leak the fd on the (common) no-daemon-yet path
            raise
        return c

    port, token = _read_endpoint(path)  # OSError if absent/corrupt, before any socket
    c = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    c.settimeout(timeout)
    try:
        c.connect(("127.0.0.1", port))
        c.sendall(token.encode("ascii"))
        # The ack proves we reached OUR daemon and not some unrelated service that
        # inherited this ephemeral port after ours died.
        if _recvn(c, 1) != b"\x01":
            raise ConnectionRefusedError(f"endpoint {path} is not our daemon")
    except OSError:
        c.close()
        raise
    return c


class Server:
    """A bound listener plus the endpoint bookkeeping the daemons need."""

    def __init__(self, sock, path, token):
        self._sock = sock
        self.path = path
        self.token = token

    def accept(self, timeout=DEFAULT_CONN_TIMEOUT):
        """Accept one authenticated client.

        Returns the connection, or None when the peer failed the token check — the
        caller should simply continue its loop. `socket.timeout` propagates, which is
        how the daemons detect idleness and exit.

        The per-connection timeout matters on both platforms: the accept loop is
        single-threaded, so a peer that connects and then says nothing would otherwise
        wedge the daemon forever."""
        conn, _ = self._sock.accept()
        if self.token is None:
            conn.settimeout(timeout)
            return conn
        # Short deadline for the handshake so a peer that connects and says nothing
        # stalls the single-threaded loop for seconds, not minutes; the generous
        # request timeout applies only once it has proved it is ours.
        conn.settimeout(HANDSHAKE_TIMEOUT)
        try:
            if _recvn(conn, TOKEN_LEN) != self.token.encode("ascii"):
                conn.close()
                return None
            conn.sendall(b"\x01")
        except OSError:
            conn.close()
            return None
        conn.settimeout(timeout)
        return conn

    def close(self):
        try:
            self._sock.close()
        except OSError:
            pass

    def unlink(self):
        """Remove the endpoint, but ONLY if it still refers to this server.

        A redundant daemon that lost the publication race, or one that idled out after
        a newer daemon took over, must not delete the live daemon's endpoint: every
        later client would then see no endpoint, spawn yet another daemon, and pay the
        model load again."""
        if self.token is None:
            unlink(self.path)  # POSIX: we own the socket file we bound
            return
        try:
            _, token = _read_endpoint(self.path)
        except OSError:
            return  # already gone or unreadable; nothing of ours to remove
        if token == self.token:
            unlink(self.path)


def _publish(path, port, token):
    """Claim the endpoint by EXCLUSIVE create, so exactly one daemon can own it.

    bind(("127.0.0.1", 0)) always succeeds, so unlike an AF_UNIX bind it cannot itself
    refuse a second daemon; this is where that refusal happens instead.

    An existing file ALWAYS loses us the race — we never probe-and-clear it here. A
    probe can only ask "did the owner answer within the timeout", and a live daemon
    busy encoding a large batch does not (the accept loop is single-threaded). Treating
    that as death would delete a live daemon's endpoint and strand every later client.
    A genuinely stale file is cleared elsewhere and costs at most one respawn: the
    daemon's own probe_live() before the model load, or the client's ECONNREFUSED
    unlink on its next connect."""
    try:
        # 0o600: the token is the access control on the loopback transport, so keep it
        # owner-only in case TEMP is ever redirected somewhere shared.
        fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    except FileExistsError:
        raise DaemonAlreadyRunning(path) from None
    with os.fdopen(fd, "wb") as fh:
        fh.write(f"{port}\n{token}\n".encode("ascii"))


def serve(path, backlog=16, idle=None):
    """Bind, claim the endpoint, and return a Server.

    Raises DaemonAlreadyRunning when another daemon claimed the endpoint while this
    one was loading its model — the caller should exit quietly."""
    if HAS_UNIX:
        sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        sock.bind(path)  # EADDRINUSE here is the POSIX single-owner guarantee
        token = None
    else:
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        # Windows lets another process steal a bound port via SO_REUSEADDR unless the
        # owner asks for exclusivity; SO_REUSEADDR is NOT the same flag as on POSIX.
        if hasattr(socket, "SO_EXCLUSIVEADDRUSE"):
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_EXCLUSIVEADDRUSE, 1)
        sock.bind(("127.0.0.1", 0))  # loopback only — never reachable off the host
        token = secrets.token_hex(TOKEN_LEN // 2)
    sock.listen(backlog)
    if token is not None:
        try:
            _publish(path, sock.getsockname()[1], token)
        except BaseException:
            sock.close()
            raise
    if idle is not None:
        sock.settimeout(idle)
    return Server(sock, path, token)


def unlink(path):
    """Best-effort endpoint removal (clearing a stale endpoint).

    A failure other than "already gone" is reported: an endpoint nobody can delete
    makes every daemon lose the exclusive create, which pins retrieval to the slow
    inline path forever. That degrades correctly but never recovers, so it must not be
    invisible."""
    try:
        os.unlink(path)
    except FileNotFoundError:
        pass
    except OSError as e:
        print(f"daemon_ipc: cannot remove endpoint {path}: {e}"
              " (retrieval will stay on the slower inline path)", file=sys.stderr)


def probe_live(path, timeout=5.0):
    """True when a live daemon already answers at `path`. A dead daemon's leftover
    endpoint is removed, so the caller can bind/publish cleanly.

    Only errors that actually PROVE death clear the endpoint: a refused connection and
    a missing file. A timeout does not — the accept loop is single-threaded, so a
    daemon busy encoding a batch cannot complete the token handshake, and deleting its
    endpoint would orphan a live daemon holding a loaded model. This is the same
    reasoning `_publish` relies on; a probe can only ask "did the owner answer within
    the timeout", never "is the owner dead". On an inconclusive probe we report not-live
    WITHOUT unlinking, so a competing daemon loses the exclusive create and exits."""
    if not os.path.exists(path):
        return False
    try:
        connect(path, timeout=timeout).close()
        return True
    except (ConnectionRefusedError, FileNotFoundError):
        unlink(path)  # nothing is listening / the endpoint vanished: provably dead
        return False
    except OSError:
        # Inconclusive (timeout, reset, …) — leave the endpoint alone.
        # KNOWN RESIDUAL: if our daemon died AND a foreign service inherited the
        # recycled port AND it accepts, swallows the token and neither replies nor
        # hangs up, nothing ever clears this file, so retrieval stays on the inline
        # path. Far narrower than treating every timeout as death (which fired under
        # ordinary load), and it degrades slow rather than wrong. Closing it properly
        # means making liveness decidable rather than inferred — publish the daemon's
        # pid beside port+token and check process existence here.
        return False


def spawn_detached(argv):
    """Start a daemon that outlives this client process. Raises on failure."""
    kw = {"stdout": subprocess.DEVNULL, "stderr": subprocess.DEVNULL}
    if os.name == "nt":
        # Windows has no start_new_session; DETACHED_PROCESS + a new process group is
        # the same intent (survive the parent, own no console window).
        kw["creationflags"] = (getattr(subprocess, "DETACHED_PROCESS", 0x00000008)
                               | getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0x00000200))
    else:
        kw["start_new_session"] = True
    subprocess.Popen(argv, **kw)
