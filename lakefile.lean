import Lake
open Lake DSL

package «corelib_verification» {
  -- add package configuration options here
}

require Aegis from git
  "git@github.com:lindy-labs/aegis.git" @ "327826726e9bca03363a52b300b6ea28f17db358"

@[default_target]
lean_lib «CorelibVerification» {
  -- add library configuration options here
}
