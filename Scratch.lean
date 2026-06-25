import Lean
import TraceParse

/-- Lean.Elab.ConfigEval.declareCoreConfigElab -/
#guard_msgs (substring := true, drop trace, check all) in
#parse:command +format "declare_core_config_elab"
