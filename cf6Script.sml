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
  pairTheory pred_setTheory categoryTheory
  cf0Theory cf1Theory cf2Theory cf4Theory cf5Theory

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

Theorem tensor_comm:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ⇒
  tensor c d ≅ tensor d c -: chu w
Proof
  rw[iso_objs_thm]
  \\ qabbrev_tac`me = λc d e.
        let m = decode_morphism d (swap c) e in
          encode_morphism
            (mk_chu_morphism c (swap d)
              <| map_agent := m.map.map_env;
                 map_env := m.map.map_agent |>)`
  \\ qexists_tac`mk_chu_morphism (tensor c d) (tensor d c)
        <| map_agent := λp. encode_pair (SND(decode_pair p), FST(decode_pair p));
           map_env := me c d |>`
  \\ qmatch_goalsub_abbrev_tac`iso _ f`
  \\ `c.world = w ∧ d.world = w` by fs[chu_objects_def]
  \\ `∀c d m. m :- d → swap c -: chu w ⇒
          ∃z. me c d (encode_morphism m) = encode_morphism z ∧
              me d c (encode_morphism z) = encode_morphism m ∧
              z :- c → swap d -: chu w ∧
              ∀a b. a ∈ c.agent ∧ b ∈ d.agent ⇒
                c.eval a (z.map.map_env b) = d.eval b (m.map.map_env a)`
  by (
    rpt gen_tac \\ strip_tac
    \\ simp[Abbr`me`, mk_chu_morphism_def, restrict_def]
    \\ qmatch_goalsub_abbrev_tac`encode_morphism z`
    \\ qexists_tac`z` \\ simp[]
    \\ conj_tac
    >- (
      AP_TERM_TAC
      \\ simp[morphism_component_equality]
      \\ fs[maps_to_in_chu]
      \\ simp[chu_morphism_map_component_equality, FUN_EQ_THM]
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
      \\ simp[maps_to_in_chu]
      \\ fs[is_chu_morphism_def, extensional_def]
      \\ simp[Abbr`z`]
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
      \\ simp[maps_to_in_chu, is_chu_morphism_def, extensional_def]
      \\ rw[] )
    \\ fs[maps_to_in_chu, Abbr`z`]
    \\ fs[is_chu_morphism_def, extensional_def]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[maps_to_in_chu, is_chu_morphism_def, extensional_def] )
  \\ simp[chu_iso_bij]
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ reverse conj_tac >- simp[Abbr`f`]
    \\ simp[is_chu_morphism_def]
    \\ conj_tac >- simp[Abbr`f`, mk_chu_morphism_def]
    \\ conj_tac >- simp[Abbr`f`, mk_chu_morphism_def]
    \\ conj_tac >- (
      simp[tensor_def, PULL_EXISTS, hom_def, Abbr`f`, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ metis_tac[] )
    \\ conj_tac >- (
      simp[Abbr`f`, mk_chu_morphism_def, restrict_def]
      \\ simp[tensor_def, PULL_EXISTS] )
    \\ simp[tensor_def, mk_cf_def, PULL_EXISTS, EXISTS_PROD, hom_def]
    \\ rpt gen_tac
    \\ strip_tac
    \\ reverse IF_CASES_TAC >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[Abbr`f`, mk_chu_morphism_def, restrict_def, tensor_def, hom_def]
      \\ metis_tac[] )
    \\ reverse IF_CASES_TAC >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[Abbr`f`, mk_chu_morphism_def, restrict_def, tensor_def]
      \\ metis_tac[] )
    \\ ntac 2 (pop_assum kall_tac)
    \\ first_x_assum drule
    \\ strip_tac \\ simp[Abbr`f`, mk_chu_morphism_def, tensor_def, restrict_def, hom_def]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[])
  \\ conj_tac
  >- (
    simp[BIJ_IFF_INV]
    \\ fs[maps_to_in_chu, is_chu_morphism_def]
    \\ qexists_tac`λp. encode_pair (SND(decode_pair p), FST(decode_pair p))`
    \\ simp[Abbr`f`, mk_chu_morphism_def, tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ rw[restrict_def] \\ fs[] )
  \\ reverse conj_tac >- fs[maps_to_in_chu]
  \\ simp[BIJ_IFF_INV]
  \\ conj_tac >- fs[maps_to_in_chu, is_chu_morphism_def]
  \\ pop_assum mp_tac
  \\ simp[maps_to_in_chu]
  \\ strip_tac
  \\ simp[tensor_def, PULL_EXISTS, hom_def]
  \\ qexists_tac`me d c`
  \\ simp[Abbr`f`, mk_chu_morphism_def, tensor_def, restrict_def, hom_def, PULL_EXISTS]
  \\ rw[]
  \\ metis_tac[]
QED

Theorem tensor_cf1[simp]:
  c ∈ chu_objects w ⇒
  tensor c (cf1 w w) ≅ c -: chu w ∧
  tensor (cf1 w w) c ≅ c -: chu w
Proof
  `∀c. c ∈ chu_objects w ⇒ c ≅ tensor c (cf1 w w) -: chu w` suffices_by
    metis_tac[tensor_comm, cf1_in_chu_objects,
              in_chu_objects_finite_world, SUBSET_REFL,
              iso_objs_trans, iso_objs_sym, is_category_chu]
  \\ rw[iso_objs_thm]
  \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
  \\ qexists_tac`mk_chu_morphism c (tensor c (cf1 w w))
       <| map_agent := λa. encode_pair (a, "");
          map_env := λm. (decode_morphism c (swap (cf1 w w)) m).map.map_env "" |>`
  \\ qmatch_goalsub_abbrev_tac`iso _ i`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[Abbr`i`, mk_chu_morphism_def]
    \\ simp[is_chu_morphism_def] \\ simp[restrict_def]
    \\ simp[tensor_def, PULL_EXISTS, hom_def, mk_cf_def]
    \\ gen_tac \\ strip_tac
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ rfs[chu_objects_def, maps_to_in_chu, is_chu_morphism_def] )
  \\ simp[chu_iso_bij]
  \\ conj_tac
  >- (
    simp[Abbr`i`, BIJ_IFF_INV, mk_chu_morphism_def, restrict_def]
    \\ simp[tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ qexists_tac`FST o decode_pair`
    \\ simp[] )
  \\ reverse conj_tac >- fs[maps_to_in_chu]
  \\ simp[BIJ_DEF]
  \\ conj_tac
  >- (
    simp[INJ_DEF]
    \\ conj_tac >- fs[maps_to_in_chu, is_chu_morphism_def]
    \\ simp[Abbr`i`, mk_chu_morphism_def, restrict_def]
    \\ simp[tensor_def, PULL_EXISTS, hom_def]
    \\ rpt gen_tac \\ strip_tac
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ rfs[chu_objects_def]
    \\ rw[]
    \\ AP_TERM_TAC
    \\ simp[morphism_component_equality, chu_morphism_map_component_equality]
    \\ fs[maps_to_in_chu, is_chu_morphism_def, extensional_def]
    \\ simp[FUN_EQ_THM]
    \\ fs[cf1_def, mk_cf_def]
    \\ metis_tac[] )
  \\ simp[SURJ_DEF]
  \\ fs[maps_to_in_chu, is_chu_morphism_def]
  \\ rw[tensor_def, PULL_EXISTS, hom_def]
  \\ qexists_tac`mk_chu_morphism i.dom (swap (cf1 w w))
       <| map_agent := flip i.dom.eval x;
          map_env := K x |>`
  \\ simp[maps_to_in_chu]
  \\ rfs[chu_objects_def]
  \\ simp[mk_chu_morphism_def, restrict_def]
  \\ simp[Abbr`i`, mk_chu_morphism_def]
  \\ simp[tensor_def, hom_def, restrict_def]
  \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ rfs[chu_objects_def]
    \\ simp[is_chu_morphism_def, extensional_def]
    \\ simp[cf1_def, mk_cf_def]
    \\ rfs[mk_chu_morphism_def, restrict_def]
    \\ rfs[wf_def] )
  \\ simp[]
  \\ fs[maps_to_in_chu]
  \\ rw[]
  \\ `F` suffices_by rw[]
  \\ pop_assum mp_tac \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`encode_morphism z`
  \\ qexists_tac`z`
  \\ simp[Abbr`z`]
QED

Definition tensor_morphism_def:
  tensor_morphism f g =
    mk_chu_morphism (tensor f.dom g.dom) (tensor f.cod g.cod)
      <| map_agent := λp. let (a,b) = decode_pair p in
                            encode_pair (f.map.map_agent a, g.map.map_agent b);
         map_env := λe. let m = decode_morphism f.cod (swap g.cod) e in
           encode_morphism
             (mk_chu_morphism f.dom (swap g.dom)
               <| map_agent := g.map.map_env o m.map.map_agent o f.map.map_agent;
                  map_env := f.map.map_env o m.map.map_env o g.map.map_agent |>) |>
End

Theorem tensor_morphism_maps_to:
  f :- c1 → c2 -: chu w ∧
  g :- d1 → d2 -: chu w
  ⇒
  tensor_morphism f g :- tensor c1 d1 → tensor c2 d2 -: chu w
Proof
  reverse(rw[maps_to_in_chu])
  >- rw[tensor_morphism_def]
  >- rw[tensor_morphism_def]
  \\ `f.dom.world = w ∧ f.cod.world = w ∧ g.dom.world = w ∧ g.cod.world = w` by fs[chu_objects_def]
  \\ simp[is_chu_morphism_def]
  \\ conj_tac >- simp[tensor_morphism_def, mk_chu_morphism_def]
  \\ conj_tac >- simp[tensor_morphism_def, mk_chu_morphism_def]
  \\ conj_asm1_tac >- (
    simp[tensor_morphism_def, mk_chu_morphism_def, restrict_def]
    \\ simp[tensor_def, PULL_EXISTS, hom_def]
    \\ gen_tac \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`encode_morphism m`
    \\ qexists_tac`m` \\ simp[]
    \\ simp[maps_to_in_chu]
    \\ simp[Abbr`m`]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[is_chu_morphism_def]
    \\ simp[extensional_def]
    \\ fs[is_chu_morphism_def, maps_to_in_chu] )
  \\ conj_asm1_tac >- (
    simp[tensor_morphism_def, mk_chu_morphism_def, restrict_def]
    \\ simp[tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ fs[is_chu_morphism_def] )
  \\ qx_genl_tac[`a`,`e`]
  \\ strip_tac
  \\ first_x_assum drule
  \\ first_x_assum drule
  \\ ntac 2 (pop_assum mp_tac)
  \\ simp[tensor_def, mk_cf_def, hom_def, PULL_EXISTS, EXISTS_PROD]
  \\ rpt strip_tac
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ pop_assum kall_tac
  \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
  \\ qmatch_rename_tac`f.dom.eval a1 (m2.map.map_env a2) =
                       f.cod.eval b1 (m1.map.map_env b2)`
  \\ qpat_x_assum`_ = encode_pair _`mp_tac
  \\ qpat_x_assum`_ = encode_morphism _`mp_tac
  \\ simp[tensor_morphism_def, mk_chu_morphism_def, tensor_def, restrict_def, hom_def]
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ pop_assum kall_tac
  \\ qmatch_goalsub_abbrev_tac`encode_morphism m3`
  \\ strip_tac
  \\ `decode_morphism f.dom (swap g.dom) (encode_morphism m3) =
      decode_morphism f.dom (swap g.dom) (encode_morphism m2)` by metis_tac[]
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
  \\ conj_tac >- (
    simp[maps_to_in_chu]
    \\ simp[Abbr`m3`]
    \\ simp[is_chu_morphism_def]
    \\ simp[extensional_def]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
    \\ pop_assum kall_tac
    \\ fs[maps_to_in_chu, is_chu_morphism_def])
  \\ disch_then(strip_assume_tac o SYM)
  \\ disch_then(strip_assume_tac o GSYM)
  \\ fs[maps_to_in_chu, is_chu_morphism_def]
  \\ simp[Abbr`m3`]
  \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
  \\ fs[maps_to_in_chu, is_chu_morphism_def]
QED

Theorem iso_tensor_right:
  c1 ≅ c2 -: chu w ∧ d ∈ chu_objects w ⇒
  tensor c1 d ≅ tensor c2 d -: chu w
Proof
  simp[iso_objs_thm, GSYM AND_IMP_INTRO]
  \\ disch_then(qx_choose_then`f`strip_assume_tac)
  \\ strip_tac
  \\ qexists_tac`tensor_morphism f (id_in (chu w) d)`
  \\ conj_asm1_tac >- simp[tensor_morphism_maps_to, id_maps_to, is_category_chu, chu_obj]
  \\ fs[chu_iso_bij]
  \\ simp[Once CONJ_ASSOC]
  \\ reverse conj_tac >- fs[maps_to_in_chu]
  \\ fs[maps_to_in_chu] \\ rfs[]
  \\ rpt(qpat_x_assum`T`kall_tac)
  \\ qpat_x_assum`BIJ _.map.map_env _ _`mp_tac
  \\ qpat_x_assum`BIJ _.map.map_agent _ _`mp_tac
  \\ ntac 2 (pop_assum kall_tac)
  \\ `c1.world = w ∧ c2.world = w ∧ d.world = w` by fs[chu_objects_def]
  \\ simp[BIJ_IFF_INV, PULL_EXISTS]
  \\ qx_gen_tac`fa` \\ strip_tac
  \\ qx_gen_tac`fe` \\ strip_tac
  \\ qabbrev_tac`f' = mk_chu_morphism c2 c1 <| map_agent := fa; map_env := fe |>`
  \\ qexists_tac`(tensor_morphism f' (id d -: chu w)).map.map_agent`
  \\ qexists_tac`(tensor_morphism f' (id d -: chu w)).map.map_env`
  \\ conj_tac
  >- (
    fs[is_chu_morphism_def]
    \\ fs[tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ fs[tensor_morphism_def, Abbr`f'`, mk_chu_morphism_def, restrict_def,
          tensor_def, chu_id_morphism_map_def] )
  \\ conj_tac >- fs[is_chu_morphism_def]
  \\ qhdtm_x_assum`is_chu_morphism` kall_tac
  \\ conj_tac >- (
    fs[Abbr`f'`, tensor_morphism_def, mk_chu_morphism_def, restrict_def, tensor_def, hom_def,
       chu_id_morphism_map_def, PULL_EXISTS]
    \\ qx_gen_tac`m` \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`encode_morphism p`
    \\ qexists_tac`p` \\ simp[]
    \\ fs[Abbr`p`, maps_to_in_chu]
    \\ fs[is_chu_morphism_def]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[maps_to_in_chu, is_chu_morphism_def]
    \\ simp[extensional_def, restrict_def]
    \\ metis_tac[] )
  \\ conj_tac
  >- (
    fs[Abbr`f'`, tensor_morphism_def, mk_chu_morphism_def, restrict_def, tensor_def, hom_def,
       chu_id_morphism_map_def, PULL_EXISTS]
    \\ qx_gen_tac`m` \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`encode_morphism p`
    \\ `p :- c1 → swap d -: chu w`
    by (
      simp[Abbr`p`, maps_to_in_chu, is_chu_morphism_def]
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
      \\ fs[maps_to_in_chu, is_chu_morphism_def]
      \\ rw[extensional_def, restrict_def] )
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ AP_TERM_TAC
    \\ simp[morphism_component_equality]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
    \\ conj_tac >- fs[maps_to_in_chu]
    \\ conj_tac >- fs[maps_to_in_chu]
    \\ simp[chu_morphism_map_component_equality, FUN_EQ_THM, PULL_FORALL]
    \\ rpt gen_tac
    \\ conj_tac
    \\ (reverse IF_CASES_TAC >- fs[maps_to_in_chu, is_chu_morphism_def, extensional_def])
    \\ (reverse IF_CASES_TAC >- (fs[maps_to_in_chu, is_chu_morphism_def] \\ metis_tac[]))
    \\ simp[Abbr`p`]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
    \\ rw[]
    \\ rfs[maps_to_in_chu, is_chu_morphism_def] )
  >- (
    fs[Abbr`f'`, tensor_morphism_def, mk_chu_morphism_def, restrict_def, tensor_def, hom_def,
       chu_id_morphism_map_def, PULL_EXISTS]
    \\ qx_gen_tac`m` \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`encode_morphism p`
    \\ `p :- c2 → swap d -: chu w`
    by (
      simp[Abbr`p`, maps_to_in_chu, is_chu_morphism_def]
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
      \\ fs[maps_to_in_chu, is_chu_morphism_def]
      \\ rw[extensional_def, restrict_def]
      \\ metis_tac[])
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ AP_TERM_TAC
    \\ simp[morphism_component_equality]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
    \\ conj_tac >- fs[maps_to_in_chu]
    \\ conj_tac >- fs[maps_to_in_chu]
    \\ simp[chu_morphism_map_component_equality, FUN_EQ_THM, PULL_FORALL]
    \\ rpt gen_tac
    \\ conj_tac
    \\ (reverse IF_CASES_TAC >- fs[maps_to_in_chu, is_chu_morphism_def, extensional_def])
    \\ TRY (reverse IF_CASES_TAC >- (fs[maps_to_in_chu, is_chu_morphism_def] \\ metis_tac[]))
    \\ simp[Abbr`p`]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
    \\ rw[]
    \\ rfs[maps_to_in_chu, is_chu_morphism_def] )
QED

Theorem iso_tensor:
  c1 ≅ c2 -: chu w ∧ d1 ≅ d2 -: chu w ⇒
  tensor c1 d1 ≅ tensor c2 d2 -: chu w
Proof
  strip_tac
  \\ irule iso_objs_trans \\ simp[]
  \\ qexists_tac`tensor c2 d1`
  \\ conj_tac >- metis_tac[iso_tensor_right, chu_obj, is_category_chu, iso_objs_objs]
  \\ irule iso_objs_trans \\ simp[]
  \\ qexists_tac`tensor d1 c2`
  \\ conj_tac >- metis_tac[tensor_comm, iso_objs_objs, is_category_chu, chu_obj]
  \\ irule iso_objs_trans \\ simp[]
  \\ qexists_tac`tensor d2 c2`
  \\ conj_tac >- metis_tac[iso_tensor_right, chu_obj, is_category_chu, iso_objs_objs]
  \\ metis_tac[tensor_comm, iso_objs_objs, is_category_chu, chu_obj]
QED

Overload pas[local] = ``λa b. IMAGE encode_pair (a × b)``

Definition tensor_assoc_helper_def:
  tensor_assoc_helper w c1 c2 c3 =
    mk_cf <| world := w;
             agent := pas c1.agent (pas c2.agent c3.agent);
             env := IMAGE (λ(g1, g2, g3).
                      encode_pair (encode_function (pas c2.agent c3.agent) g1,
                        encode_pair (encode_function (pas c1.agent c3.agent) g2,
                                     encode_function (pas c1.agent c2.agent) g3)))
                      { (g1, g2, g3) |
                    extensional g1 (pas c2.agent c3.agent) ∧ IMAGE g1 (pas c2.agent c3.agent) ⊆ c1.env ∧
                    extensional g2 (pas c1.agent c3.agent) ∧ IMAGE g2 (pas c1.agent c3.agent) ⊆ c2.env ∧
                    extensional g3 (pas c1.agent c2.agent) ∧ IMAGE g3 (pas c1.agent c2.agent) ⊆ c3.env ∧
                        (∀a1 a2 a3. a1 ∈ c1.agent ∧ a2 ∈ c2.agent ∧ a3 ∈ c3.agent ⇒
                           c1.eval a1 (g1 (encode_pair (a2, a3))) =
                           c2.eval a2 (g2 (encode_pair (a1, a3))) ∧
                           c2.eval a2 (g2 (encode_pair (a1, a3))) =
                           c3.eval a3 (g3 (encode_pair (a1, a2)))) };
             eval := λa e. c1.eval (FST (decode_pair a))
                             ((decode_function (FST (decode_pair e))) (SND (decode_pair a))) |>
End

Theorem tensor_assoc_helper_in_chu_objects[simp]:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ c3 ∈ chu_objects w ⇒
  tensor_assoc_helper w c1 c2 c3 ∈ chu_objects w
Proof
  simp[tensor_assoc_helper_def]
  \\ strip_tac
  \\ simp[chu_objects_def]
  \\ conj_tac
  >- (
    simp[image_def, SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
    \\ fs[chu_objects_def, wf_def] \\ fs[]
    \\ rpt gen_tac \\ strip_tac
    \\ first_x_assum irule \\ simp[]
    \\ DEP_REWRITE_TAC[decode_encode_function]
    \\ fs[finite_cf_def] )
  \\ fs[chu_objects_def]
  \\ `finite_cf c1 ∧ finite_cf c2 ∧ finite_cf c3` by metis_tac[wf_def]
  \\ fs[finite_cf_def] \\ rfs[]
  \\ irule IMAGE_FINITE
  \\ qmatch_goalsub_abbrev_tac`extensional _ d1 ∧ IMAGE _ _ ⊆ r1 ∧
                               extensional _ d2 ∧ IMAGE _ _ ⊆ r2 ∧
                               extensional _ d3 ∧ IMAGE _ _ ⊆ r3 ∧ _`
  \\ qabbrev_tac`fns = λd r. { g : string -> string | extensional g d ∧ IMAGE g d ⊆ r }`
  \\ irule SUBSET_FINITE
  \\ qexists_tac`fns d1 r1 × fns d2 r2 × fns d3 r3`
  \\ reverse conj_tac
  >- ( simp[SUBSET_DEF, PULL_EXISTS, Abbr`fns`] )
  \\ `∀d r. FINITE d ∧ FINITE r ⇒ FINITE (fns d r)`
  suffices_by  (
    `FINITE d1 ∧ FINITE d2 ∧ FINITE d3` by simp[Abbr`d1`,Abbr`d2`,Abbr`d3`]
    \\ simp[] )
  \\ rw[Abbr`fns`]
  \\ qspec_then`λg. IMAGE (λx. (x, g x)) d`irule FINITE_INJ
  \\ qexists_tac`d`
  \\ qexists_tac`POW (d × r)`
  \\ simp[INJ_DEF, IN_POW]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
  \\ simp[extensional_def]
  \\ rw[FUN_EQ_THM]
  \\ metis_tac[]
QED

Definition swap_pair_def:
  swap_pair p = encode_pair (SND(decode_pair p),FST(decode_pair p))
End

Definition map_pair_def:
  map_pair f g p = encode_pair (f (FST (decode_pair p)), g (SND (decode_pair p)))
End

Definition swap_pair_fn_def:
  swap_pair_fn a b g = restrict (g o swap_pair) (pas b a)
End

Definition swap_pair_efn_def:
  swap_pair_efn a b g = encode_function (pas b a) (swap_pair_fn a b (decode_function g))
End

Theorem swap_pair_efn_encode_function:
  FINITE a ∧ FINITE b ∧ extensional f (pas a b) ⇒
  swap_pair_efn a b (encode_function (pas a b) f) =
    encode_function (pas b a) (swap_pair_fn a b f)
Proof
  rw[swap_pair_efn_def, swap_pair_fn_def]
QED

Theorem tensor_assoc_helper_swap_iso[simp]:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ c3 ∈ chu_objects w ⇒
  tensor_assoc_helper w c1 c2 c3 ≅ tensor_assoc_helper w c1 c3 c2 -: chu w
Proof
  rw[iso_objs_thm]
  \\ `finite_cf c1 ∧ finite_cf c2 ∧ finite_cf c3` by ( fs[chu_objects_def] \\ metis_tac[wf_def])
  \\ `c1.world = w ∧ c2.world = w ∧ c3.world = w` by fs[chu_objects_def]
  \\ qexists_tac`mk_chu_morphism (tensor_assoc_helper w c1 c2 c3) (tensor_assoc_helper w c1 c3 c2)
       <| map_agent := map_pair I swap_pair;
          map_env := map_pair (swap_pair_efn c3.agent c2.agent) swap_pair |>`
  \\ simp[maps_to_in_chu]
  \\ fs[finite_cf_def]
  \\ conj_asm1_tac
  >- (
    simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_tac
    >- (
      simp[tensor_assoc_helper_def, EXISTS_PROD, PULL_EXISTS]
      \\ qx_genl_tac[`x`,`y`,`z`]
      \\ strip_tac
      \\ map_every qexists_tac[`swap_pair_fn c3.agent c2.agent x`,`z`,`y`]
      \\ simp[swap_pair_fn_def, map_pair_def, swap_pair_def, swap_pair_efn_def]
      \\ fs[extensional_def, SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
      \\ fs[restrict_def, swap_pair_def] )
    \\ conj_tac >- ( simp[tensor_assoc_helper_def, swap_pair_def, map_pair_def,
                          PULL_EXISTS, EXISTS_PROD] )
    \\ simp[tensor_assoc_helper_def, mk_cf_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[map_pair_def, swap_pair_def, swap_pair_efn_encode_function]
    \\ rpt gen_tac \\ strip_tac
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[]
      \\ qmatch_goalsub_abbrev_tac`encode_function _ ff` \\ qexists_tac`ff` \\ simp[Abbr`ff`]
      \\ qmatch_goalsub_abbrev_tac`encode_function _ ff` \\ qexists_tac`ff` \\ simp[Abbr`ff`]
      \\ qmatch_goalsub_abbrev_tac`encode_function _ ff` \\ qexists_tac`ff` \\ simp[Abbr`ff`]
      \\ simp[swap_pair_fn_def]
      \\ simp[restrict_def, PULL_EXISTS, EXISTS_PROD, swap_pair_def]
      \\ fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD] )
    \\ pop_assum kall_tac
    \\ reverse IF_CASES_TAC
    >- metis_tac[]
    \\ pop_assum kall_tac
    \\ DEP_REWRITE_TAC[decode_encode_function]
    \\ simp[swap_pair_fn_def]
    \\ simp[restrict_def, swap_pair_def] )
  \\ simp[chu_iso_bij]
  \\ simp[mk_chu_morphism_def]
  \\ simp[BIJ_IFF_INV]
  \\ simp[restrict_def]
  \\ simp[PULL_EXISTS]
  \\ qexists_tac`map_pair I swap_pair`
  \\ qexists_tac`map_pair (swap_pair_efn c2.agent c3.agent) swap_pair`
  \\ simp[tensor_assoc_helper_def, PULL_EXISTS, EXISTS_PROD]
  \\ simp[map_pair_def, swap_pair_def, swap_pair_efn_encode_function]
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ rpt(qmatch_goalsub_abbrev_tac`encode_function _ ff` \\ qexists_tac`ff` \\ simp[Abbr`ff`])
    \\ simp[swap_pair_fn_def]
    \\ simp[restrict_def, PULL_EXISTS, EXISTS_PROD, swap_pair_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD] )
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ rpt(qmatch_goalsub_abbrev_tac`encode_function _ ff` \\ qexists_tac`ff` \\ simp[Abbr`ff`])
    \\ simp[swap_pair_fn_def]
    \\ simp[restrict_def, PULL_EXISTS, EXISTS_PROD, swap_pair_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD] )
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ DEP_REWRITE_TAC[swap_pair_efn_encode_function]
    \\ simp[swap_pair_fn_def]
    \\ simp[restrict_def, PULL_EXISTS, EXISTS_PROD, swap_pair_def]
    \\ AP_TERM_TAC
    \\ simp[FUN_EQ_THM]
    \\ rw[] \\ fs[]
    \\ fs[extensional_def, PULL_EXISTS, EXISTS_PROD] )
  \\ rpt gen_tac \\ strip_tac
  \\ reverse IF_CASES_TAC
  >- (
    `F` suffices_by rw[]
    \\ pop_assum mp_tac
    \\ simp[]
    \\ rpt(qmatch_goalsub_abbrev_tac`encode_function _ ff` \\ qexists_tac`ff` \\ simp[Abbr`ff`])
    \\ simp[swap_pair_fn_def]
    \\ simp[restrict_def, PULL_EXISTS, EXISTS_PROD, swap_pair_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD] )
  \\ pop_assum kall_tac
  \\ DEP_REWRITE_TAC[swap_pair_efn_encode_function]
  \\ simp[swap_pair_fn_def]
  \\ simp[restrict_def, PULL_EXISTS, EXISTS_PROD, swap_pair_def]
  \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]
  \\ rw[] \\ fs[]
  \\ fs[extensional_def, PULL_EXISTS, EXISTS_PROD]
QED

Theorem tensor_assoc:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ c3 ∈ chu_objects w ⇒
  tensor c1 (tensor c2 c3) ≅ tensor (tensor c1 c2) c3 -: chu w
Proof
  `∀c1 c2 c3.
    c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ c3 ∈ chu_objects w ⇒
    tensor (tensor c1 c2) c3 ≅ tensor (tensor c1 c3) c2 -: chu w`
  suffices_by (
    rpt strip_tac
    \\ irule iso_objs_trans \\ simp[]
    \\ qexists_tac`tensor c1 (tensor c3 c2)`
    \\ conj_tac >- ( irule iso_tensor \\ simp[] \\ irule tensor_comm \\ simp[] )
    \\ irule iso_objs_trans \\ simp[]
    \\ qexists_tac`tensor (tensor c3 c2) c1`
    \\ conj_tac >- metis_tac[tensor_comm, tensor_in_chu_objects]
    \\ irule iso_objs_trans \\ simp[]
    \\ qexists_tac`tensor (tensor c3 c1) c2`
    \\ conj_tac >- metis_tac[]
    \\ irule iso_objs_trans \\ simp[]
    \\ qexists_tac`tensor (tensor c1 c3) c2`
    \\ conj_tac >- ( irule iso_tensor \\ simp[] \\ irule tensor_comm \\ simp[] )
    \\ metis_tac[] )
  \\ `∃d. ∀c1 c2 c3.
        c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ c3 ∈ chu_objects w ⇒
        tensor (tensor c1 c2) c3 ≅ d c1 c2 c3 -: chu w ∧
        d c1 c2 c3 ≅ d c1 c3 c2 -: chu w`
  suffices_by metis_tac[iso_objs_sym, iso_objs_trans, is_category_chu]
  \\ qexists_tac`tensor_assoc_helper w`
  \\ rw[]
  \\ cheat
QED

(*
Theorem homotopy_equiv_tensor_right:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ d ∈ chu_objects w ∧
  c1 ≃ c2 -: w ⇒
  tensor c1 d ≃ tensor c2 d -: w
*)

val _ = export_theory();
