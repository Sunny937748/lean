import Lake
open Lake DSL

package «my_project» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[⟨`pp.unicode.fun, true⟩] -- pretty-prints `fun a ↦ b`

-- 添加 Mathlib 依赖
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MyProject» where
  -- add any library configuration options here
