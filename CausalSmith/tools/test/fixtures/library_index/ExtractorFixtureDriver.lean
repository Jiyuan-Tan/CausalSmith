import LibraryIndexCore

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [srcRoot, outPath] =>
      runIndex `ExtractorRangeFixture.Extension `ExtractorRangeFixture srcRoot outPath
        #[`ExtractorRangeFixture.Extension]
      return 0
  | _ =>
      IO.eprintln "usage: ExtractorFixtureDriver <fixture-source-root> <output-json>"
      return 2
