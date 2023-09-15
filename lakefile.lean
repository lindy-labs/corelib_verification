import Lake
open Lake DSL

package «corelib_verification» {
  -- add package configuration options here
}

require Aegis from git
  "git@github.com:lindy-labs/aegis.git" @ "7ed537e1e62e95c352805d92cef27b2b8a5ab6a6"

@[default_target]
lean_lib «CorelibVerification» {
  -- add library configuration options here
}
