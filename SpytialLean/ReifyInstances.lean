module

public import SpytialLean.ReifyCore
public import SpytialLean.Tier1Exposure
public meta import SpytialLean.ReifyDeriving

namespace SpytialLean

/- These instances decode the constructor and field schema emitted by the existing relationalizer. -/
deriving instance SpytialReify for Bool, PUnit, Int
deriving instance SpytialReify for Option, Prod, Sum, List

end SpytialLean
