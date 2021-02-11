(*
Copyright 2021 DeepMind Technologies Limited.

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
  combinTheory pairTheory listTheory pred_setTheory helperSetTheory categoryTheory
  cf0Theory cf1Theory cf2Theory cf3Theory cf4Theory

val _ = new_theory"cf5";

Definition subagent_def:
  subagent w c d ⇔ c ∈ chu_objects w ∧ d ∈ chu_objects w ∧
    ∀m. m :- c → cfbot w w -: chu w ⇒
      ∃m1 m2. m1 :- c → d -: chu w ∧ m2 :- d → cfbot w w -: chu w ∧ m = m2 o m1 -: chu w
End


Overload "subagent_syntax" = ``λc d w. subagent w c d``

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
  \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
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

Definition covering_subagent_def:
  covering_subagent w c d ⇔
    c ∈ chu_objects w ∧ d ∈ chu_objects w ∧
    ∀e. e ∈ c.env ⇒
      ∃f m. f ∈ d.env ∧ m :- c → d -: chu w ∧ e = m.map.map_env f
End

Theorem subagent_covering:
  c ◁ d -: w ⇔ covering_subagent w c d
Proof
  rw[subagent_def, covering_subagent_def]
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

Definition currying_subagent_def:
  currying_subagent w c d ⇔
    c ∈ chu_objects w ∧ d ∈ chu_objects w ∧
    ∃z. z ∈ chu_objects d.agent ∧ c ≃ move d z -: w
End

Theorem hom_finite[simp]:
  finite_cf c ∧ finite_cf d ⇒
  FINITE (chu w | c → d |)
Proof
  rw[hom_def, maps_to_in_chu, finite_cf_def]
  \\ qspec_then`λm. (m.map.map_agent, m.map.map_env)`irule FINITE_INJ
  \\ qexists_tac`{f | extensional f c.agent ∧ IMAGE f c.agent ⊆ d.agent} ×
                 {f | extensional f d.env ∧ IMAGE f d.env ⊆ c.env}`
  \\ reverse conj_tac
  >- (
    simp[INJ_DEF]
    \\ conj_tac
    >- ( simp[is_chu_morphism_def] \\ simp[PULL_EXISTS, SUBSET_DEF] )
    \\ simp[chu_morphism_map_component_equality, morphism_component_equality] )
  \\ irule FINITE_CROSS
  \\ conj_tac
  THENL [qspec_then`λf. IMAGE (λx. (x, f x)) c.agent`irule FINITE_INJ
         \\ qexists_tac`c` \\ qexists_tac`POW (c.agent × d.agent)`,
         qspec_then`λf. IMAGE (λx. (x, f x)) d.env`irule FINITE_INJ
         \\ qexists_tac`d` \\ qexists_tac`POW (d.env × c.env)`]
  \\ simp[]
  \\ simp[INJ_DEF, IN_POW]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[EXTENSION, PULL_EXISTS, FORALL_PROD]
  \\ simp[FUN_EQ_THM, extensional_def]
  \\ metis_tac[]
QED

Definition encode_morphism_def:
  encode_morphism m =
    encode_pair (encode_function m.dom.agent m.map.map_agent,
                 encode_function m.cod.env m.map.map_env)
End

Definition decode_morphism_def:
  decode_morphism c d s =
    <| dom := c; cod := d; map := <| map_agent := decode_function (FST (decode_pair s));
                                     map_env := decode_function (SND (decode_pair s)) |> |>
End

Theorem decode_encode_morphism[simp]:
  m.dom = c ∧ m.cod = d ∧ FINITE c.agent ∧ FINITE d.env ∧
  extensional m.map.map_agent c.agent ∧
  extensional m.map.map_env d.env
  ⇒
  decode_morphism c d (encode_morphism m) = m
Proof
  rw[morphism_component_equality, decode_morphism_def]
  \\ rw[chu_morphism_map_component_equality]
  \\ rw[encode_morphism_def]
QED

Theorem decode_encode_chu_morphism[simp]:
  m :- c → d -: chu w ⇒
  decode_morphism c d (encode_morphism m) = m
Proof
  rw[maps_to_in_chu, is_chu_morphism_def]
  \\ irule decode_encode_morphism
  \\ fs[chu_objects_def, wf_def]
  \\ fs[finite_cf_def]
QED

(*
Definition encode_hom_def:
  encode_hom w c d = encode_list (MAP encode_morphism (SET_TO_LIST (chu w | c → d |)))
End

Definition decode_hom_def:
  decode_hom c d s = set (MAP (decode_morphism c d) (decode_list s))
End

Theorem decode_encode_hom[simp]:
  finite_cf c ∧ finite_cf d ⇒
  decode_hom c d (encode_hom w c d) = chu w | c → d |
Proof
  rw[decode_hom_def, EXTENSION, MEM_MAP, encode_hom_def, PULL_EXISTS]
  \\ rw[EQ_IMP_THM]
  \\ TRY(qexists_tac`x` \\ simp[])
  \\ DEP_REWRITE_TAC[decode_encode_morphism]
  \\ fs[hom_def, maps_to_in_chu, finite_cf_def]
  \\ fs[is_chu_morphism_def]
QED
*)

Theorem covering_implies_currying:
  covering_subagent w c d ⇒ currying_subagent w c d
Proof
  rw[covering_subagent_def, currying_subagent_def]
  \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
  \\ `finite_cf c ∧ finite_cf d` by fs[chu_objects_def, wf_def]
  \\ qexists_tac`mk_cf <| world := d.agent; agent := c.agent;
                          env := IMAGE encode_morphism (chu w |c → d|);
                          eval := λa m. (decode_morphism c d m).map.map_agent a |>`
  \\ conj_asm1_tac
  >- (
    simp[chu_objects_def]
    \\ conj_tac
    >- (
      simp[SUBSET_DEF, image_def, PULL_EXISTS]
      \\ rw[hom_def]
      \\ fs[maps_to_in_chu, finite_cf_def, is_chu_morphism_def] )
    \\ simp[finite_cf_def]
    \\ fs[chu_objects_def]
    \\ metis_tac[hom_finite, wf_def, finite_cf_def, IMAGE_FINITE])
  \\ qmatch_assum_abbrev_tac`z ∈ chu_objects d.agent`
  \\ simp[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism c (move d z)
       <| map_agent := I;
          map_env := λx. (decode_morphism c d (FST (decode_pair x))).map.map_env
                           (SND (decode_pair x)) |>`
  \\ qmatch_goalsub_abbrev_tac`f :- c → move d z -: _`
  \\ qexists_tac`mk_chu_morphism (move d z) c
       <| map_agent := I;
          map_env := λe.
            let p = @p. (FST p).map.map_env (SND p) = e ∧ (FST p) :- c → d -: chu w ∧
                        (SND p) ∈ d.env
            in encode_pair (encode_morphism (FST p), SND p) |>`
  \\ qmatch_goalsub_abbrev_tac`g :- move d z → _ -: _`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, Abbr`f`]
    \\ simp[mk_chu_morphism_def]
    \\ simp[is_chu_morphism_def, PULL_EXISTS, FORALL_PROD]
    \\ simp[restrict_def]
    \\ simp[Abbr`z`, PULL_EXISTS]
    \\ CONV_TAC(LAND_CONV(RESORT_FORALL_CONV(sort_vars["x"])))
    \\ CONV_TAC(RAND_CONV(RESORT_FORALL_CONV(sort_vars["x"])))
    \\ simp[GSYM FORALL_AND_THM]
    \\ gen_tac
    \\ Cases_on`x ∈ chu w |c → d|` \\ simp[]
    \\ simp[mk_cf_def]
    \\ gen_tac
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ DEP_REWRITE_TAC[decode_encode_morphism]
    \\ fs[hom_def, maps_to_in_chu, is_chu_morphism_def, finite_cf_def] )
  \\ conj_asm1_tac
  >- (
    simp[Once maps_to_in_chu, Abbr`g`]
    \\ simp[mk_chu_morphism_def]
    \\ simp[is_chu_morphism_def]
    \\ simp[restrict_def]
    \\ qmatch_goalsub_abbrev_tac`a ∧ b ∧ x`
    \\ `b` by simp[Abbr`b`, Abbr`z`]
    \\ qunabbrev_tac`b`
    \\ simp[]
    \\ simp[Abbr`a`, Abbr`x`]
    \\ CONV_TAC(RAND_CONV(SWAP_FORALL_CONV))
    \\ simp[GSYM FORALL_AND_THM]
    \\ qx_gen_tac`e`
    \\ Cases_on`e ∈ c.env` \\ simp[]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- ( simp[EXISTS_PROD] \\ metis_tac[] )
    \\ simp[FORALL_PROD]
    \\ qx_gen_tac`g`
    \\ qx_gen_tac`x`
    \\ strip_tac
    \\ simp[Abbr`z`]
    \\ conj_asm1_tac >- (simp[hom_def] \\ metis_tac[])
    \\ simp[mk_cf_def, move_def]
    \\ gen_tac \\ strip_tac
    \\ DEP_REWRITE_TAC[decode_encode_morphism]
    \\ fs[maps_to_in_chu, is_chu_morphism_def, finite_cf_def]
    \\ rpt BasicProvers.VAR_EQ_TAC
    \\ simp[] )
  \\ imp_res_tac maps_to_comp \\ fs[]
  \\ conj_tac \\ irule homotopic_id
  \\ fs[maps_to_in_chu, pre_chu_def]
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ DEP_REWRITE_TAC[chu_comp]
  \\ fs[composable_in_def, pre_chu_def]
  \\ simp[Abbr`f`, Abbr`g`, mk_chu_morphism_def]
  \\ simp[restrict_def, FUN_EQ_THM, Abbr`z`]
QED

Theorem subagent_same_homotopy_equiv:
  c1 ◁ d -: w ∧ c1 ≃ c2 -: w ⇒ c2 ◁ d -: w
Proof
  rw[subagent_covering]
  \\ fs[covering_subagent_def]
  \\ fs[homotopy_equiv_def]
  \\ conj_asm1_tac >- fs[maps_to_in_chu]
  \\ gen_tac \\ strip_tac
  \\ first_assum(qspec_then`f.map.map_env e`mp_tac)
  \\ impl_tac >- ( fs[maps_to_in_chu, is_chu_morphism_def] )
  \\ disch_then(qx_choosel_then[`x`,`m`]strip_assume_tac)
  \\ qexists_tac`x` \\ simp[]
  \\ qexists_tac`mk_chu_morphism c2 d
       <| map_agent := m.map.map_agent o g.map.map_agent;
          map_env := (x =+ e)(g.map.map_env o m.map.map_env) |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ imp_res_tac maps_to_comp \\ fs[]
    \\ qpat_assum`m o g -: _ :- _ → _ -: _`mp_tac
    \\ qpat_assum`homotopic w (f o g -: _) _`mp_tac
    \\ DEP_REWRITE_TAC[compose_in_thm]
    \\ DEP_REWRITE_TAC[compose_thm]
    \\ DEP_REWRITE_TAC[chu_comp]
    \\ simp[CONJ_ASSOC]
    \\ conj_tac >- fs[maps_to_in_chu, composable_in_def, pre_chu_def]
    \\ simp[maps_to_in_chu, pre_chu_def, homotopic_def, hom_comb_def]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def, chu_id_morphism_map_def]
    \\ simp[restrict_def, APPLY_UPDATE_THM]
    \\ rw[] \\ fs[] \\ rw[] \\ fs[]
    \\ metis_tac[] )
  \\ simp[mk_chu_morphism_def]
  \\ simp[restrict_def, APPLY_UPDATE_THM]
QED

Theorem currying_implies_covering_eq_case:
  d ∈ chu_objects w ∧
  z ∈ chu_objects d.agent ∧
  e ∈ (move d z).env ⇒
  ∃f m. f ∈ d.env ∧ m :- move d z → d -: chu w ∧ e = m.map.map_env f
Proof
  simp[EXISTS_PROD, PULL_EXISTS]
  \\ qx_genl_tac[`x`,`f`] \\ rw[]
  \\ qexists_tac`f`
  \\ qexists_tac`mk_chu_morphism (move d z) d
       <| map_agent := flip z.eval x;
          map_env := λf. encode_pair (x, f) |>`
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[mk_chu_morphism_def]
    \\ simp[is_chu_morphism_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[restrict_def]
    \\ fs[chu_objects_def, wf_def] \\ fs[] )
  \\ simp[mk_chu_morphism_def]
  \\ simp[restrict_def]
QED

Theorem currying_implies_covering:
  currying_subagent w c d ⇒ covering_subagent w c d
Proof
  rw[currying_subagent_def, covering_subagent_def]
  \\ Cases_on`c = move d z`
  >- metis_tac[currying_implies_covering_eq_case]
  \\ imp_res_tac homotopy_equiv_sym
  \\ first_assum(mp_then Any mp_tac subagent_same_homotopy_equiv)
  \\ simp[subagent_covering]
  \\ simp[covering_subagent_def, PULL_EXISTS, EXISTS_PROD]
  \\ disch_then irule
  \\ rw[]
  \\ PROVE_TAC[SIMP_RULE(srw_ss())[EXISTS_PROD]currying_implies_covering_eq_case]
QED

Theorem subagent_currying:
  (c ◁ d -: w ⇔ currying_subagent w c d)
Proof
  metis_tac[subagent_covering, currying_implies_covering, covering_implies_currying]
QED

Theorem homotopy_equiv_move_swap_cf1:
  c ∈ chu_objects w ⇒
  c ≃ move c (swap (cf1 c.agent c.agent)) -: w
Proof
  rw[homotopy_equiv_def]
  \\ `FINITE c.agent` by (fs[chu_objects_def] \\ metis_tac[wf_def, finite_cf_def])
  \\ qexists_tac`mk_chu_morphism c (move c (swap (cf1 c.agent c.agent)))
      <| map_agent := I; map_env := SND o decode_pair |>`
  \\ qexists_tac`mk_chu_morphism(move c (swap (cf1 c.agent c.agent))) c
      <| map_agent := I; map_env := λe. encode_pair("", e) |>`
  \\ conj_asm1_tac
  >- (
    simp[mk_chu_morphism_def, maps_to_in_chu]
    \\ simp[is_chu_morphism_def, PULL_EXISTS, EXISTS_PROD]
    \\ rw[move_def, restrict_def]
    \\ rw[cf1_def, mk_cf_def] )
  \\ conj_asm1_tac
  >- (
    simp[mk_chu_morphism_def, maps_to_in_chu]
    \\ simp[is_chu_morphism_def, PULL_EXISTS, EXISTS_PROD]
    \\ rw[move_def, restrict_def]
    \\ rw[cf1_def, mk_cf_def] )
  \\ qmatch_goalsub_abbrev_tac`f o g -: _`
  \\ imp_res_tac maps_to_comp \\ fs[]
  \\ conj_tac \\ irule homotopic_id
  \\ fs[maps_to_in_chu, pre_chu_def]
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ DEP_REWRITE_TAC[chu_comp]
  \\ fs[composable_in_def, pre_chu_def]
  \\ simp[Abbr`f`, Abbr`g`, mk_chu_morphism_def]
  \\ simp[restrict_def, FUN_EQ_THM]
QED

Theorem homotopy_equiv_subagent:
  c1 ≃ c2 -: w ⇒ c1 ◁ c2 -: w
Proof
  simp[subagent_currying, currying_subagent_def]
  \\ strip_tac
  \\ imp_res_tac homotopy_equiv_in_chu_objects \\ simp[]
  \\ qexists_tac`swap (cf1 c2.agent c2.agent)`
  \\ `FINITE c2.agent` by (fs[chu_objects_def] \\ metis_tac[wf_def, finite_cf_def])
  \\ simp[]
  \\ irule homotopy_equiv_trans
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ simp[homotopy_equiv_move_swap_cf1]
QED

Theorem subagent_refl[simp]:
  c ∈ chu_objects w ⇒  c ◁ c -: w
Proof
  metis_tac[homotopy_equiv_refl, homotopy_equiv_subagent]
QED

Theorem subagent_trans:
  c1 ◁ c2 -: w ∧ c2 ◁ c3 -: w ⇒ c1 ◁ c3 -: w
Proof
  rw[subagent_def]
  \\ first_x_assum(first_x_assum o mp_then Any strip_assume_tac)
  \\ first_x_assum(first_x_assum o mp_then Any strip_assume_tac)
  \\ imp_res_tac maps_to_comp \\ fs[]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ irule comp_assoc
  \\ fs[maps_to_in_chu, composable_in_def, pre_chu_def]
QED

Theorem subagent_homotopy_equiv:
  c1 ◁ d1 -: w ∧ c1 ≃ c2 -: w ∧ d1 ≃ d2 -: w ⇒
  c2 ◁ d2 -: w
Proof
  metis_tac[homotopy_equiv_subagent, homotopy_equiv_sym, subagent_trans]
QED

Definition mutual_subagents_def:
  mutual_subagents w c d ⇔ c ◁ d -: w ∧ d ◁ c -: w
End

Theorem mutual_subagents_refl[simp]:
  c ∈ chu_objects w ⇒ mutual_subagents w c c
Proof
  metis_tac[mutual_subagents_def, subagent_refl]
QED

Theorem mutual_subagents_sym:
  mutual_subagents w c d ⇔ mutual_subagents w c d
Proof
  rw[mutual_subagents_def]
QED

Theorem mutual_subagents_trans:
  mutual_subagents w c1 c2 ∧ mutual_subagents w c2 c3 ⇒ mutual_subagents w c1 c3
Proof
  metis_tac[mutual_subagents_def, subagent_trans]
QED

Theorem homotopy_equiv_mutual_subagents:
  c ≃ d -: w ⇒ mutual_subagents w c d
Proof
  rw[mutual_subagents_def]
  \\ metis_tac[homotopy_equiv_subagent, homotopy_equiv_sym]
QED

Theorem sum_cfT_cfT:
  FINITE w ⇒
    sum (cfT w) (cfT w) ≃ cfT w -: w ∧
    ¬(sum (cfT w) (cfT w) ≅ cfT w -: chu w)
Proof
  strip_tac
  \\ conj_tac
  >- (
    irule empty_env_nonempty_agent
    \\ simp[sum_def, cfT_def, cf0_def])
  \\ simp[iso_objs_thm, chu_iso_bij]
  \\ CCONTR_TAC \\ fs[]
  \\ fs[maps_to_in_chu]
  \\ `CARD f.dom.agent = CARD f.cod.agent`
  by (
    irule FINITE_BIJ_CARD
    \\ fs[chu_objects_def]
    \\ metis_tac[wf_def, finite_cf_def])
  \\ pop_assum mp_tac
  \\ simp[sum_def, cfT_def, cf0_def]
  \\ simp[CARD_UNION_EQN, SING_INTER]
QED

Theorem mutual_subagents_cfT_null:
  FINITE w ⇒ mutual_subagents w (cfT w) (null w)
Proof
  rw[mutual_subagents_def, subagent_covering, covering_subagent_def]
  \\ fs[cfT_def, null_def, cf0_def]
QED

Theorem cfT_not_homotopy_equiv_null:
  ¬(cfT w ≃ null w -: w)
Proof
  rw[homotopy_equiv_def]
  \\ CCONTR_TAC \\ fs[]
  \\ fs[maps_to_in_chu, is_chu_morphism_def]
  \\ fs[null_def, cfT_def, cf0_def]
QED

Theorem cfT_subagent[simp]:
  c ∈ chu_objects w ⇒ cfT w ◁ c -: w
Proof
  strip_tac
  \\ imp_res_tac in_chu_objects_finite_world
  \\ rw[subagent_def]
  \\ fs[cfT_def, cf0_def, maps_to_in_chu, is_chu_morphism_def, cfbot_def]
QED

Theorem subagent_cfbot[simp]:
  c ∈ chu_objects w ⇒ c ◁ cfbot w w -: w
Proof
  strip_tac
  \\ imp_res_tac in_chu_objects_finite_world
  \\ rw[subagent_def]
  \\ qexists_tac`m`
  \\ qexists_tac`id (cfbot w w) -: chu w`
  \\ simp[]
  \\ irule(GSYM id_comp2)
  \\ fs[maps_to_in_chu, pre_chu_def]
QED

Theorem null_subagent[simp]:
  c ∈ chu_objects w ⇒ null w ◁ c -: w
Proof
  metis_tac[cfT_subagent, mutual_subagents_cfT_null, mutual_subagents_def,
            subagent_trans, in_chu_objects_finite_world]
QED

Theorem subagent_cfbot_image:
  c ∈ chu_objects w ∧ s ⊆ w ⇒
  (c ◁ cfbot w s -: w ⇔ image c ⊆ s)
Proof
  strip_tac
  \\ imp_res_tac in_chu_objects_finite_world
  \\ EQ_TAC
  >- (
    CCONTR_TAC \\ fs[SUBSET_DEF]
    \\ fs[image_def]
    \\ fs[subagent_covering, covering_subagent_def]
    \\ first_x_assum drule
    \\ rw[]
    \\ CCONTR_TAC \\ fs[]
    \\ fs[maps_to_in_chu]
    \\ fs[is_chu_morphism_def]
    \\ qmatch_asmsub_abbrev_tac`c.eval a e`
    \\ `c.eval a e = (cfbot w s).eval (m.map.map_agent a) f` by metis_tac[]
    \\ pop_assum mp_tac
    \\ simp_tac(srw_ss())[cfbot_def, cf1_def, mk_cf_def]
    \\ fs[cfbot_def, cf1_def, mk_cf_def]
    \\ metis_tac[])
  \\ rw[subagent_covering, covering_subagent_def]
  \\ qexists_tac`""`
  \\ qexists_tac`mk_chu_morphism c (cfbot w s) <| map_agent := flip c.eval e; map_env := K e |>`
  \\ simp[maps_to_in_chu]
  \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
  \\ simp[cfbot_def, restrict_def]
  \\ simp[cf1_def, mk_cf_def]
  \\ fs[SUBSET_DEF, image_def, PULL_EXISTS]
QED

Theorem obs_homotopy_equiv_prod_subagent:
  c ∈ chu_objects w ⇒
  (s ∈ obs c ⇔
   s ⊆ w ∧ ∃c1 c2. c1 ◁ cfbot w s -: w ∧ c2 ◁ cfbot w (w DIFF s) -: w ∧
                   c ≃ c1 && c2 -: w)
Proof
  strip_tac
  \\ drule obs_homotopy_equiv_prod
  \\ simp[]
  \\ disch_then kall_tac
  \\ Cases_on`s ⊆ w` \\ simp[]
  \\ EQ_TAC \\ strip_tac
  \\ map_every qexists_tac[`c1`,`c2`]
  \\ simp[subagent_cfbot_image]
  \\ DEP_REWRITE_TAC[GSYM subagent_cfbot_image]
  \\ simp[]
  \\ fs[subagent_def]
QED

val _ = export_theory();
