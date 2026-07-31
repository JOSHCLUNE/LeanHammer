module

public import Hammer.Tactic
public import Hammer.DuperCore
public import Hammer.HammerCore
public import Hammer.Options
public import Hammer.SingleRuleTac
/- Everything `hammer` provides runs during elaboration, so its dependencies have to be available
   at compile time as well. -/
public meta import Hammer.Tactic
public meta import Hammer.DuperCore
public meta import Hammer.HammerCore
public meta import Hammer.Options
public meta import Hammer.SingleRuleTac
