import Lean
import TraceParse

/-- Lean.Elab.ConfigEval.declareCoreConfigElab -/
#guard_msgs (error, substring := true) in
#parse:command +format "declare_core_config_elab"
