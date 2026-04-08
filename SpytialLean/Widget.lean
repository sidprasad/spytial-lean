import Lean.Widget.UserWidget
import SpytialLean.Types

namespace SpytialLean

open Lean Widget

/-- The Spytial widget module, rendering relational data as a spatial diagram.
    The JS is built from `widget/src/spytialWidget.tsx` via rollup. -/
@[widget_module]
def SpytialWidget : Widget.Module where
  javascript := include_str ".." / ".lake" / "build" / "js" / "spytialWidget.js"

end SpytialLean
