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

open HolKernel boolLib bossLib Parse
     pred_setTheory categoryTheory
     cf0Theory cf1Theory cf2Theory

val _ = new_theory"cf3";

Theorem ensure_cf1_morphism:
  (s ∈ ensure c ⇔ s ⊆ c.world ∧ ∃m. is_chu_morphism (cf1 c.world s) c m)
Proof
  rw[ensure_def, is_chu_morphism_def]
  \\ Cases_on`s ⊆ c.world` \\ simp[]
  \\ simp[extensional_def, cf1_def, mk_cf_def]
  \\ rw[EQ_IMP_THM]
  >- (
    qexists_tac`<| map_agent := λx. if x = "" then a else ARB;
                   map_env := λe. if e ∈ c.env then c.eval a e else ARB |>`
    \\ rw[] \\ fs[SUBSET_DEF] \\ metis_tac[] )
  \\ qexists_tac`m.map_agent ""` \\ rw[]
  \\ metis_tac[]
QED

Theorem prevent_cf1_morphism:
  c ∈ chu_objects w ⇒
  (s ∈ prevent c ⇔ s ⊆ w ∧ ∃m. is_chu_morphism (cf1 w (w DIFF s)) c m)
Proof
  rw[chu_objects_def]
  \\ reverse(Cases_on`s ⊆ c.world` \\ simp[])
  >- simp[prevent_def]
  \\ `s ∈ prevent c ⇔ c.world DIFF s ∈ ensure c`
  by (
    rw[prevent_def, ensure_def]
    \\ fs[SUBSET_DEF, wf_def]
    \\ metis_tac[] )
  \\ pop_assum SUBST1_TAC
  \\ rw[ensure_cf1_morphism]
QED

Theorem ensure_morphism_mono:
  m :- c → d -: chu w ⇒ ensure c ⊆ ensure d
Proof
  rw[SUBSET_DEF]
  \\ fs[ensure_cf1_morphism]
  \\ qmatch_assum_rename_tac`is_chu_morphism _ c f1`
  \\ imp_res_tac maps_to_obj \\ fs[]
  \\ `w = c.world ∧ w = d.world` by fs[chu_objects_def]
  \\ qabbrev_tac`m1 = <| dom := cf1 w x; cod := c; map := f1 |>`
  \\ `m1 :- cf1 w x → c -: chu w`
  by ( simp[maps_to_in_def, Abbr`m1`] \\ fs[pre_chu_def] )
  \\ `m o m1 -: chu w :- cf1 w x → d -: chu w` by (
    imp_res_tac maps_to_comp \\ fs[] )
  \\ fs[maps_to_in_def, pre_chu_def]
  \\ metis_tac[]
QED

val _ = export_theory();
