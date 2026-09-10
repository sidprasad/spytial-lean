module

public meta import Lean

namespace SpytialLean

/-- Request kernel-checked reconstruction of the exact datum emitted by a command or
`relationalize%`. Disabled by default so existing open-term and non-Tier-1 inspection is unchanged.
Certification neither changes identity nor substitutes another graph when checking fails. -/
public meta register_option spytial.certifyReification : Bool := {
  defValue := false
  descr := "kernel-check reconstruction of the actual emitted closed Tier 1 datum"
}

end SpytialLean
