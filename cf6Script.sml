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

open HolKernel boolLib bossLib Parse dep_rewrite
  pairTheory categoryTheory
  cf0Theory cf1Theory cf5Theory

val _ = new_theory"cf6";

Definition tensor_def:
  tensor c d = mk_cf <|
    world := c.world;
    agent := IMAGE encode_pair (c.agent × d.agent);
    env := IMAGE encode_morphism (hom (chu c.world) c (swap d));
    eval := λa e. c.eval (FST(decode_pair a))
                    ((decode_morphism c (swap d) e).map.map_env (SND(decode_pair a))) |>
End

Theorem finite_tensor[simp]:
  finite_cf c ∧ finite_cf d ⇒ finite_cf (tensor c d)
Proof
  simp[finite_cf_def, tensor_def]
QED

Theorem wf_tensor[simp]:
  c.world = d.world ∧ wf c ∧ wf d ⇒ wf (tensor c d)
Proof
  simp[wf_def]
  \\ strip_tac
  \\ simp[tensor_def, mk_cf_def, PULL_EXISTS, EXISTS_PROD, hom_def]
  \\ rw[]
  \\ imp_res_tac decode_encode_chu_morphism \\ fs[] \\ rfs[]
  \\ fs[maps_to_in_chu, is_chu_morphism_def]
  \\ metis_tac[]
QED

Theorem tensor_in_chu_objects[simp]:
  c ∈ chu_objects w ∧
  d ∈ chu_objects w ⇒
  tensor c d ∈ chu_objects w
Proof
  rw[chu_objects_def]
  \\ rw[tensor_def]
QED

(* TODO: tensor example with J, K, L *)

(*
Theorem tensor_comm:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ⇒
  tensor c d ≅ tensor d c -: chu w
Proof
  rw[iso_objs_thm]
  \\ qexists_tac`mk_chu_morphism (tensor c d) (tensor d c)
        <| map_agent := λp. encode_pair (SND(decode_pair p), FST(decode_pair p));
           map_env := λe. let m = decode_morphism c (swap d) e in
                            encode_morphism
                              (mk_chu_morphism d (swap c)
                               <| map_agent := m.map.map_env;
                                  map_env := m.map.map_agent |>) |>`
  \\ qmatch_goalsub_abbrev_tac`iso _ f`
  \\ simp[chu_iso_bij]
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ reverse conj_tac >- simp[Abbr`f`]
    \\ simp[is_chu_morphism_def]
    \\ simp[Abbr`f`, mk_chu_morphism_def]
    \\ simp[tensor_def, mk_cf_def, PULL_EXISTS, EXISTS_PROD, hom_def]
*)

val _ = export_theory();
