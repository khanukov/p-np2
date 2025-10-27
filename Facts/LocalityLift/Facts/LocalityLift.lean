import Facts.LocalityLift.Exports

/-!
  Entry point for the stand-alone locality-lift package.  Downstream
  repositories should depend on this module instead of cherry-picking the files
  under `Interface/`.
-/

namespace Facts
namespace LocalityLift

-- The namespace is intentionally left empty: all useful declarations live in
-- the imported interface files.  The module serves as a stable entry point for
-- Lake packages.

end LocalityLift
end Facts
