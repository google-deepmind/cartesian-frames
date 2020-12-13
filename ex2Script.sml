(*
Copyright 2020 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

open HolKernel boolLib bossLib boolSimps Parse
  rich_listTheory categoryTheory cf0Theory cf1Theory cf2Theory

val _ = new_theory"ex2";

Definition sym_cf_def:
  sym_cf = mk_cf
    <| world := {"";"."};
       agent := {"";"."};
       env := {"";"."};
       eval := λa e. if a = e then "." else "" |>
End

Definition flip_morphism_def:
  flip_morphism = mk_chu_morphism sym_cf sym_cf
    <| map_agent := λa. REPLICATE (1 - LENGTH a) #"." ;
       map_env := λe. REPLICATE (1 - LENGTH e) #"."  |>
End

Theorem flip_morphism_dom_cod[simp]:
  flip_morphism.dom = sym_cf ∧
  flip_morphism.cod = sym_cf
Proof
  EVAL_TAC
QED

Theorem sym_cf_in_chu_objects[simp]:
  sym_cf ∈ chu_objects sym_cf.world
Proof
  rw[chu_objects_def, wf_def]
  \\ fs[sym_cf_def, mk_cf_def, finite_cf_def]
QED

Theorem is_morphism_flip[simp]:
  is_chu_morphism sym_cf sym_cf flip_morphism.map
Proof
  rw[is_chu_morphism_def, flip_morphism_def, mk_chu_morphism_def, sym_cf_def]
  \\ rw[restrict_def, REPLICATE_compute, mk_cf_def]
QED

Theorem not_homotopic_flip_id:
  ¬ homotopic sym_cf.world flip_morphism (id sym_cf -: chu sym_cf.world)
Proof
  rw[homotopic_def]
  \\ simp[pre_chu_def]
  \\ rw[hom_comb_def]
  \\ rw[is_chu_morphism_def]
  \\ ntac 4 disj2_tac
  \\ qexists_tac`""`
  \\ qexists_tac`""`
  \\ EVAL_TAC
QED

val _ = export_theory();
