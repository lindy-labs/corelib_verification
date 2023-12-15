import Lake
open Lake DSL

package «corelib_verification» {
  -- add package configuration options here
}

require aegis from git
  "git@github.com:lindy-labs/aegis.git" @ "main"

@[default_target]
lean_lib «CorelibVerification» {
  -- add library configuration options here
}
