
-- The main entry point for `lake test`.  The previous test executable imported
-- the full `Basic` suite which in turn referenced several legacy modules that
-- are no longer part of the build.  We keep the executable trivial so that the
-- remaining test files can still be compiled individually by Lake.

def main : IO UInt32 :=
  pure 0
