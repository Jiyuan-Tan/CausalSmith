"""Round-trip probe for scripts/daemon_ipc.py, driven by test/retrieval_transport.test.ts.

argv[1] picks the transport: "native" uses whatever the platform gives (AF_UNIX here),
"tcp" forces the WINDOWS transport by clearing HAS_UNIX. Forcing it is the only way a
POSIX CI box can cover the loopback-TCP branch that Windows always takes.

Prints "OK <transport>" on a clean serve -> probe -> echo -> teardown cycle.
"""
import os
import sys
import threading

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "scripts"))
import daemon_ipc  # noqa: E402

mode = sys.argv[1]
if mode == "tcp":
    daemon_ipc.HAS_UNIX = False
expect_suffix = ".sock" if daemon_ipc.HAS_UNIX else ".port"

ep = daemon_ipc.endpoint("selftest", f"{os.getpid()}|{mode}")
assert ep.endswith(expect_suffix), f"{ep} should end with {expect_suffix}"
assert not daemon_ipc.probe_live(ep), "a never-published endpoint must not look live"

# A corrupt/stale endpoint must read as dead AND be cleared, so the next daemon binds
# clean. Every shape below once escaped as a NON-OSError (UnicodeDecodeError from the
# raw bytes, ValueError from a Unicode digit that str.isdigit accepts but int() rejects),
# which is the exact bug class this module exists to prevent.
for corrupt in (b"not-a-port", b"\xff\xfe\x90", "\u00b2\n".encode("utf-8"), b"99999\nshort", b""):
    with open(ep, "wb") as fh:
        fh.write(corrupt)
    try:
        live = daemon_ipc.probe_live(ep)
    except OSError:
        raise SystemExit(f"probe_live must swallow OSError for {corrupt!r}")
    except Exception as e:
        raise SystemExit(f"probe_live raised non-OSError {type(e).__name__} for {corrupt!r}: {e}")
    assert not live, f"corrupt endpoint {corrupt!r} must not look live"
    assert not os.path.exists(ep), f"probe_live must clear corrupt endpoint {corrupt!r}"

    with open(ep, "wb") as fh:
        fh.write(corrupt)
    try:
        daemon_ipc.connect(ep, timeout=2.0)
        raise SystemExit(f"connect to corrupt endpoint {corrupt!r} should have raised")
    except OSError:
        pass  # the only error type the clients' fallback path catches
    except Exception as e:
        raise SystemExit(f"connect raised non-OSError {type(e).__name__} for {corrupt!r}: {e}")
    daemon_ipc.unlink(ep)

srv = daemon_ipc.serve(ep, backlog=4, idle=30.0)
assert os.path.exists(ep), "serve must publish the endpoint"

# A SECOND daemon must lose. On POSIX the AF_UNIX bind refuses it; on Windows bind(port 0)
# always succeeds, so the exclusive endpoint claim is what refuses it. Without this, two
# daemons both served and the loser's idle-exit deleted the WINNER's endpoint, stranding
# every later client into another model load.
try:
    daemon_ipc.serve(ep, backlog=4, idle=30.0)
    raise SystemExit("a second serve() on a live endpoint must fail")
except (daemon_ipc.DaemonAlreadyRunning, OSError):
    pass
assert os.path.exists(ep), "the loser must not remove the winner's endpoint"


def serve_n(n):
    served = 0
    while served < n:
        conn = srv.accept()
        if conn is None:  # peer failed the token check (Windows transport)
            continue
        served += 1
        try:
            data = conn.recv(65536)
            if data:  # empty payload == health-check probe; just hang up
                conn.sendall(data)
        finally:
            conn.close()


t = threading.Thread(target=serve_n, args=(2,), daemon=True)
t.start()

assert daemon_ipc.probe_live(ep), "a bound endpoint must look live"

# A daemon that is alive but BUSY (bound, not currently in accept()) must survive a
# probe. The token handshake means such a daemon cannot answer, so a probe that treated
# "no answer" as "dead" would delete a live daemon's endpoint and orphan its loaded
# model. Note the assertion above passes for the wrong reason on its own: a thread
# parked IN accept() does answer. This case is the one that actually pins the rule.
busy = daemon_ipc.endpoint("selftest-busy", f"{os.getpid()}|{mode}|busy")
daemon_ipc.unlink(busy)
busy_srv = daemon_ipc.serve(busy, backlog=4, idle=30.0)
try:
    daemon_ipc.probe_live(busy, timeout=1.0)  # cannot answer: nothing is accepting
    assert os.path.exists(busy), "an inconclusive probe must NOT delete a live endpoint"
    # And a competing daemon must therefore lose the claim rather than take it over.
    try:
        daemon_ipc.serve(busy, backlog=4, idle=30.0)
        raise SystemExit("a competing serve() on a busy daemon's endpoint must fail")
    except (daemon_ipc.DaemonAlreadyRunning, OSError):
        pass
finally:
    busy_srv.close()
    busy_srv.unlink()

c = daemon_ipc.connect(ep, timeout=15.0)
try:
    c.sendall(b"ping\n")
    assert c.recv(64) == b"ping\n", "payload must round-trip unchanged"
finally:
    c.close()
t.join(timeout=15.0)

# A server whose endpoint was taken over by a NEWER daemon must not delete that
# daemon's file on its own idle exit — the bug that cascaded into repeated model loads.
if not daemon_ipc.HAS_UNIX:
    with open(ep, "w") as fh:
        fh.write("65000\n" + "f" * daemon_ipc.TOKEN_LEN + "\n")
    srv.unlink()
    assert os.path.exists(ep), "unlink must spare an endpoint owned by another daemon"
    daemon_ipc.unlink(ep)

srv.close()
daemon_ipc.unlink(ep)
assert not os.path.exists(ep), "unlink must remove the endpoint"

# With the endpoint gone, connect must raise OSError — the error type the clients'
# fallback-to-inline path catches. An AttributeError here is the original Windows bug.
try:
    daemon_ipc.connect(ep, timeout=2.0)
    raise SystemExit("connect to a removed endpoint should have raised")
except OSError:
    pass
except AttributeError as e:  # pragma: no cover - the regression this module exists to prevent
    raise SystemExit(f"connect raised AttributeError, not OSError: {e}")

print(f"OK {'unix' if daemon_ipc.HAS_UNIX else 'tcp'}")
