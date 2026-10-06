import LibraryIndexCore

/-! # Causalean library-index exe

Walks the elaborated environment of `import Causalean` and writes
`doc/library_index.json` for the site's `/library` explorer. Declarations of modules
unchanged since the previous run are reused from a machine-local cache under
`.lake/build/`; set `LIBRARY_INDEX_FULL` to rederive everything. -/

unsafe def main : IO Unit :=
  runIndex `Causalean `Causalean "." "doc/library_index.json"
    (cachePath := some ".lake/build/library_index_cache.json")
