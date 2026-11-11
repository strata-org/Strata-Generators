/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
-/

/-!
# A formatter for `Unit` that prints nothing
-/

open Std

/-- A formatter for `Unit` that prints nothing. Enable it per file with
    `attribute [local instance] unitToFormat`. -/
@[instance_reducible]
def unitToFormat : ToFormat Unit where
  format _ := .nil
