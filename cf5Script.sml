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
  pred_setTheory categoryTheory cf0Theory cf1Theory cf2Theory

val _ = new_theory"cf5";

Definition subagent_def:
  subagent w c d ⇔ c ∈ chu_objects w ∧ d ∈ chu_objects w ∧
    ∀m. m :- c → cfbot w w -: chu w ⇒
      ∃m1 m2. m1 :- c → d -: chu w ∧ m2 :- d → cfbot w w -: chu w ∧ m = m2 o m1 -: chu w
End


val _ = overload_on("subagent_syntax", ``λc d w. subagent w c d``);

val _ = add_rule {
  term_name = "subagent_syntax",
  fixity = Infix(NONASSOC,450),
  pp_elements = [HardSpace 1, TOK "\226\151\129", HardSpace 1, TM, HardSpace 1, TOK "-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))
};

Theorem morphisms_to_cfbot:
  c ∈ chu_objects w ⇒
  BIJ (λm. m.map.map_env "") {m | m :- c → cfbot w w -: chu w} c.env
Proof
  rw[BIJ_IFF_INV]
  >- (
    fs[maps_to_in_chu, is_chu_morphism_def]
    \\ first_x_assum irule
    \\ rw[cfbot_def] )
  \\ qexists_tac`λe. mk_chu_morphism c (cfbot w w)
       <| map_agent := flip c.eval e; map_env := K e |>`
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    rw[maps_to_in_chu]
    \\ rw[is_chu_morphism_def, mk_chu_morphism_def]
    \\ rw[restrict_def]
    \\ fs[chu_objects_def, wf_def]
    \\ fs[cfbot_def, cf1_def, mk_cf_def] )
  \\ conj_tac
  >- (
    rw[maps_to_in_chu]
    \\ rw[morphism_component_equality]
    \\ simp[chu_morphism_map_component_equality]
    \\ simp[mk_chu_morphism_def]
    \\ simp[restrict_def, FUN_EQ_THM]
    \\ fs[is_chu_morphism_def]
    \\ fs[cfbot_def, cf1_def, mk_cf_def]
    \\ fs[extensional_def]
    \\ metis_tac[] )
  \\ rw[mk_chu_morphism_def]
  \\ rw[restrict_def]
  \\ fs[cfbot_def, cf1_def, mk_cf_def]
QED

Theorem subagent_cover:
  c ◁ d -: w ⇔
    c ∈ chu_objects w ∧ d ∈ chu_objects w ∧
    ∀e. e ∈ c.env ⇒
      ∃f m. f ∈ d.env ∧ m :- c → d -: chu w ∧ e = m.map.map_env f
Proof
  rw[subagent_def]
  \\ Cases_on`c ∈ chu_objects w` \\ simp[]
  \\ Cases_on`d ∈ chu_objects w` \\ simp[]
  \\ imp_res_tac morphisms_to_cfbot
  \\ `∀P. (∀e. e ∈ c.env ⇒ P e) ⇔ (∀m. m :- c → cfbot w w -: chu w ⇒ P (m.map.map_env ""))`
  by ( fs[BIJ_IFF_INV] \\ metis_tac[] )
  \\ simp[]
  \\ ho_match_mp_tac ConseqConvTheory.forall_eq_thm
  \\ gen_tac
  \\ Cases_on`m :- c → cfbot w w -: chu w` \\ simp[]
  \\ `∀P. (∃e (x:chu_morphism). e ∈ d.env ∧ P e x) ⇔
          (∃m x. m :- d → cfbot w w -: chu w ∧ P (m.map.map_env "") x)`
  by ( fs[BIJ_IFF_INV] \\ metis_tac[] )
  \\ simp[CONJ_ASSOC]
  \\ CONV_TAC(PATH_CONV"lrbblr"(REWR_CONV CONJ_COMM))
  \\ CONV_TAC(LAND_CONV(SWAP_EXISTS_CONV))
  \\ ho_match_mp_tac ConseqConvTheory.exists_eq_thm
  \\ qx_gen_tac`n`
  \\ ho_match_mp_tac ConseqConvTheory.exists_eq_thm
  \\ qx_gen_tac`p`
  \\ Cases_on`n :- d → cfbot w w -: chu w` \\ simp[]
  \\ Cases_on`p :- c → d -: chu w` \\ simp[]
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ DEP_REWRITE_TAC[chu_comp]
  \\ fs[maps_to_in_chu, composable_in_def, pre_chu_def]
  \\ simp[morphism_component_equality]
  \\ simp[chu_morphism_map_component_equality]
  \\ simp[FUN_EQ_THM]
  \\ simp[cfbot_def]
  \\ simp[restrict_def]
  \\ first_x_assum(qspec_then`P`kall_tac)
  \\ first_x_assum(qspec_then`P`kall_tac)
  \\ qhdtm_x_assum`BIJ`kall_tac
  \\ qhdtm_x_assum`BIJ`kall_tac
  \\ rw[]
  \\ fs[cfbot_def, is_chu_morphism_def, extensional_def]
  \\ fs[cf1_def, mk_cf_def]
  \\ metis_tac[]
QED

val _ = export_theory();
