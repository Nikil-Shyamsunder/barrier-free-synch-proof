import Lake
open Lake DSL

package SemaAlloc where
  -- Package configuration

require aesop from git
  "https://github.com/leanprover-community/aesop"

@[default_target]
lean_lib SemaAlloc where
  -- Library configuration
  globs := #[.andSubmodules `SemaAlloc]
