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
    world := c.world ∪ d.world;
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
  wf c ∧ wf d ⇒ wf (tensor c d)
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
    \\ qexists_tac`tensor (tensor c2 c3) c1`
    \\ conj_tac >- metis_tac[tensor_comm, tensor_in_chu_objects]
    \\ irule iso_objs_trans \\ simp[]
    \\ qexists_tac`tensor (tensor c2 c1) c3`
    \\ conj_tac >- metis_tac[]
    \\ irule iso_tensor \\ simp[]
    \\ irule tensor_comm \\ simp[])
  \\ `∃d. ∀c1 c2 c3.
        c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ c3 ∈ chu_objects w ⇒
        tensor (tensor c1 c2) c3 ≅ d c1 c2 c3 -: chu w ∧
        d c1 c2 c3 ≅ d c1 c3 c2 -: chu w`
  suffices_by metis_tac[iso_objs_sym, iso_objs_trans, is_category_chu]
  \\ qexists_tac`tensor_assoc_helper w`
  \\ rw[]
  \\ simp[iso_objs_thm]
  \\ `c1.world = w ∧ c2.world = w ∧ c3.world = w ∧ finite_cf c1 ∧ finite_cf c2 ∧ finite_cf c3`
  by (fs[chu_objects_def] \\ metis_tac[wf_def])
  \\ rfs[finite_cf_def]
  \\ qexists_tac`mk_chu_morphism (tensor (tensor c1 c2) c3) (tensor_assoc_helper w c1 c2 c3)
       <| map_agent := λp.
            encode_pair (FST (decode_pair (FST (decode_pair p))),
              encode_pair (SND (decode_pair (FST (decode_pair p))),
                           SND (decode_pair p)));
          map_env := λe.
            let g1 = decode_function (FST (decode_pair e)) in
            let g2 = decode_function (FST (decode_pair (SND (decode_pair e)))) in
            let g3 = decode_function (SND (decode_pair (SND (decode_pair e)))) in
            encode_morphism (mk_chu_morphism (tensor c1 c2) (swap c3)
              <| map_agent := g3;
                 map_env := λa3. encode_morphism (mk_chu_morphism c1 (swap c2)
                   <| map_agent := λa1. g2 (encode_pair (a1, a3));
                      map_env := λa2. g1 (encode_pair (a2, a3)) |>) |>) |>`
  \\ qmatch_goalsub_abbrev_tac`iso _ f`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ reverse conj_tac >- simp[Abbr`f`]
    \\ simp[Abbr`f`, mk_chu_morphism_def]
    \\ qmatch_goalsub_abbrev_tac`restrict f _.env`
    \\ simp[is_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_tac
    >- (
      simp[tensor_assoc_helper_def, PULL_EXISTS]
      \\ rpt gen_tac \\ strip_tac
      \\ simp[Abbr`f`]
      \\ simp[Once tensor_def, SimpR``$IN``, hom_def]
      \\ qmatch_goalsub_abbrev_tac`encode_morphism m`
      \\ qexists_tac`m` \\ simp[]
      \\ simp[maps_to_in_chu]
      \\ `(tensor c1 c2).world = w` by simp[tensor_def]
      \\ pop_assum SUBST_ALL_TAC \\ simp[]
      \\ reverse conj_tac >- simp[Abbr`m`]
      \\ simp[is_chu_morphism_def]
      \\ simp[Abbr`m`]
      \\ simp[restrict_def]
      \\ conj_tac
      >- (
        simp[tensor_def, hom_def]
        \\ gen_tac \\ strip_tac
        \\ qmatch_goalsub_abbrev_tac`encode_morphism m`
        \\ qexists_tac`m` \\ simp[]
        \\ simp[maps_to_in_chu]
        \\ reverse conj_tac >- simp[Abbr`m`]
        \\ simp[is_chu_morphism_def]
        \\ simp[Abbr`m`]
        \\ fs[extensional_def, PULL_EXISTS, EXISTS_PROD, SUBSET_DEF] )
      \\ conj_tac
      >- ( simp[tensor_def, PULL_EXISTS, EXISTS_PROD] \\ fs[SUBSET_DEF, PULL_EXISTS] )
      \\ simp[tensor_def, mk_cf_def, PULL_EXISTS, EXISTS_PROD, hom_def]
      \\ qx_genl_tac[`e3`,`e1`,`e2`]
      \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac`encode_morphism m`
      \\ `m :- c1 → (swap c2) -: chu w`
      by (
        simp[maps_to_in_chu]
        \\ reverse conj_tac >- simp[Abbr`m`]
        \\ simp[is_chu_morphism_def]
        \\ simp[Abbr`m`]
        \\ fs[extensional_def, PULL_EXISTS, EXISTS_PROD]
        \\ fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD] )
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ pop_assum kall_tac
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
      \\ simp[]
      \\ simp[Abbr`m`] )
    \\ conj_tac
    >- ( simp[tensor_assoc_helper_def, tensor_def, PULL_EXISTS, EXISTS_PROD] )
    \\ qx_genl_tac[`a`,`e`]
    \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD, mk_cf_def, hom_def]
    \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD, mk_cf_def, hom_def]
    \\ qx_genl_tac[`a3`,`a1`,`a2`]
    \\ strip_tac
    \\ pop_assum mp_tac
    \\ simp[Abbr`f`]
    \\ qmatch_goalsub_abbrev_tac`encode_morphism f`
    \\ simp[Once tensor_assoc_helper_def, PULL_EXISTS, EXISTS_PROD]
    \\ qx_genl_tac[`g1`,`g2`,`g3`]
    \\ strip_tac
    \\ simp[tensor_assoc_helper_def, mk_cf_def, PULL_EXISTS, EXISTS_PROD]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ simp[Once tensor_def, mk_cf_def]
    \\ simp[Once tensor_def, hom_def]
    \\ simp[Once tensor_def]
    \\ `f :- tensor c1 c2 → swap c3 -: chu w`
    by (
      simp[maps_to_in_chu]
      \\ simp[Abbr`f`]
      \\ simp[is_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
      \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ qho_match_abbrev_tac`(∀e. e ∈ c3.agent ⇒ ∃x. encode_morphism (m e) = encode_morphism x ∧ _ x) ∧ _`
      \\ simp[]
      \\ `∀e. e ∈ c3.agent ⇒ m e :- c1 → swap c2 -: chu w`
      by (
        gen_tac \\ strip_tac
        \\ simp[maps_to_in_chu]
        \\ simp[Abbr`m`]
        \\ simp[is_chu_morphism_def]
        \\ simp[extensional_def]
        \\ fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD] )
      \\ conj_tac >- metis_tac[]
      \\ conj_tac >- fs[SUBSET_DEF, PULL_EXISTS]
      \\ rpt gen_tac \\ strip_tac
      \\ simp[Once tensor_def, mk_cf_def, hom_def]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ pop_assum kall_tac
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
      \\ simp[]
      \\ simp[Abbr`m`] )
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ simp[Once tensor_def, mk_cf_def, hom_def]
    \\ simp[Abbr`f`, restrict_def]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def]
      \\ simp[extensional_def]
      \\ fs[SUBSET_DEF, PULL_EXISTS] )
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ simp[] )
  \\ simp[chu_iso_bij]
  \\ simp[Once CONJ_ASSOC]
  \\ reverse conj_tac >- fs[maps_to_in_chu]
  \\ conj_tac
  >- (
    simp[BIJ_IFF_INV]
    \\ conj_tac >- fs[maps_to_in_chu, is_chu_morphism_def]
    \\ qexists_tac`λp. encode_pair
         (encode_pair (FST (decode_pair p),
                       FST (decode_pair (SND (decode_pair p)))),
          SND (decode_pair (SND (decode_pair p))))`
    \\ simp[Abbr`f`, mk_chu_morphism_def, restrict_def]
    \\ simp[tensor_assoc_helper_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[tensor_def, PULL_EXISTS, EXISTS_PROD] )
  \\ simp[BIJ_DEF]
  \\ once_rewrite_tac[CONJ_COMM]
  \\ simp[SURJ_DEF, GSYM CONJ_ASSOC]
  \\ conj_asm1_tac >- fs[maps_to_in_chu, is_chu_morphism_def]
  \\ conj_tac
  >- (
    simp[Abbr`f`, mk_chu_morphism_def, restrict_def]
    \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
    \\ simp[Once tensor_def]
    \\ qx_gen_tac`g` \\ strip_tac
    \\ qho_match_abbrev_tac`∃y. P y ∧ Q y`
    \\ `∃y. P y ∧ (P y ⇒ Q y)` suffices_by metis_tac[]
    \\ simp[Abbr`P`, Abbr`Q`]
    \\ qho_match_abbrev_tac`∃y. P y ∧ (P y ⇒ encode_morphism (m y) = _)`
    \\ `∃y. P y ∧ m y = g` suffices_by (
      strip_tac
      \\ qexists_tac`y`
      \\ simp[] )
    \\ simp[Abbr`m`, morphism_component_equality]
    \\ fs[maps_to_in_chu]
    \\ simp[Abbr`P`]
    \\ simp[chu_morphism_map_component_equality, FUN_EQ_THM]
    \\ fs[is_chu_morphism_def]
    \\ simp[tensor_assoc_helper_def, PULL_EXISTS]
    \\ qexists_tac`restrict (λp.
         (decode_morphism c1 (swap c2)
            (g.map.map_env (SND (decode_pair p)))).map.map_env (FST (decode_pair p)))
         (pas c2.agent c3.agent)`
    \\ qmatch_goalsub_abbrev_tac`extensional g1`
    \\ qexists_tac`restrict (λp.
         (decode_morphism c1 (swap c2)
            (g.map.map_env (SND (decode_pair p)))).map.map_agent (FST (decode_pair p)))
         (pas c1.agent c3.agent)`
    \\ qmatch_goalsub_abbrev_tac`extensional _ _ ∧ _ ∧ extensional g2 _ ∧ _`
    \\ qexists_tac`g.map.map_agent`
    \\ conj_tac >- simp[Abbr`g1`]
    \\ conj_tac
    >- (
      simp[Abbr`g1`, SUBSET_DEF, PULL_EXISTS, EXISTS_PROD, restrict_def]
      \\ qpat_x_assum`∀e. _ ⇒ _ ∈ (_ _ _).env`mp_tac
      \\ simp[tensor_def, hom_def] \\ strip_tac
      \\ qx_genl_tac[`a2`,`a3`] \\ strip_tac
      \\ first_x_assum(qspec_then`a3`mp_tac) \\ simp[]
      \\ strip_tac \\ simp[]
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
      \\ fs[maps_to_in_chu, is_chu_morphism_def] )
    \\ conj_tac >- simp[Abbr`g2`]
    \\ conj_tac
    >- (
      simp[Abbr`g2`, SUBSET_DEF, PULL_EXISTS, EXISTS_PROD, restrict_def]
      \\ qpat_x_assum`∀e. _ ⇒ _ ∈ (_ _ _).env`mp_tac
      \\ simp[tensor_def, hom_def] \\ strip_tac
      \\ qx_genl_tac[`a1`,`a3`] \\ strip_tac
      \\ first_x_assum(qspec_then`a3`mp_tac) \\ simp[]
      \\ strip_tac \\ simp[]
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
      \\ fs[maps_to_in_chu, is_chu_morphism_def] )
    \\ conj_tac >- fs[tensor_def]
    \\ conj_tac >- fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD, tensor_def]
    \\ conj_tac
    >- (
      rpt gen_tac \\ strip_tac
      \\ simp[Abbr`g1`, Abbr`g2`, restrict_def]
      \\ qpat_x_assum`∀e. _ ⇒ g.map.map_env _ ∈ _`(qspec_then`a3`mp_tac)
      \\ simp[tensor_def, hom_def] \\ strip_tac
      \\ simp[]
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
      \\ simp[]
      \\ conj_tac
      >- ( fs[maps_to_in_chu, is_chu_morphism_def] )
      \\ first_x_assum(qspecl_then[`encode_pair (a1,a2)`,`a3`]mp_tac)
      \\ simp[tensor_def, mk_cf_def, hom_def]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ pop_assum kall_tac
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
      \\ disch_then (SUBST1_TAC o SYM)
      \\ fs[maps_to_in_chu, is_chu_morphism_def] )
    \\ conj_tac
    >- (
      rw[]
      >- ( DEP_REWRITE_TAC[decode_encode_function] \\ fs[tensor_def] )
      \\ fs[extensional_def] )
    \\ qx_gen_tac`a3`
    \\ reverse IF_CASES_TAC
    >- fs[extensional_def]
    \\ DEP_REWRITE_TAC[decode_encode_function]
    \\ conj_tac
    >- ( fs[] \\ simp[Abbr`g2`, Abbr`g1`] )
    \\ simp[Abbr`g1`, Abbr`g2`, restrict_def]
    \\ qpat_x_assum`∀e. _ ⇒ g.map.map_env _ ∈ _`(qspec_then`a3`mp_tac)
    \\ simp[tensor_def, hom_def] \\ strip_tac
    \\ simp[]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ AP_TERM_TAC
    \\ simp[morphism_component_equality]
    \\ fs[maps_to_in_chu]
    \\ simp[chu_morphism_map_component_equality, FUN_EQ_THM]
    \\ fs[is_chu_morphism_def, extensional_def]
    \\ rw[] )
  \\ simp[INJ_DEF]
  \\ rpt gen_tac
  \\ simp[Abbr`f`, mk_chu_morphism_def, restrict_def]
  \\ strip_tac
  \\ qho_match_abbrev_tac`encode_morphism (m x) = _ (m y) ⇒ _`
  \\ strip_tac
  \\ `decode_morphism (tensor c1 c2) (swap c3) (encode_morphism (m x)) =
      decode_morphism (tensor c1 c2) (swap c3) (encode_morphism (m y))` by simp[]
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
  \\ reverse conj_tac
  >- (
    qpat_x_assum`x ∈ _`mp_tac
    \\ qpat_x_assum`y ∈ _`mp_tac
    \\ simp[tensor_assoc_helper_def, PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac
    \\ rpt gen_tac \\ strip_tac
    \\ simp[Abbr`m`, FUN_EQ_THM]
    \\ strip_tac
    \\ `g3 = g3'` by (
      simp[FUN_EQ_THM]
      \\ fs[extensional_def, tensor_def]
      \\ metis_tac[] )
    \\ `g1 = g1'` by (
      simp[FUN_EQ_THM]
      \\ qx_gen_tac`p`
      \\ reverse(Cases_on`p ∈ pas c2.agent c3.agent`) >- fs[extensional_def]
      \\ fs[EXISTS_PROD]
      \\ qmatch_assum_rename_tac`a3 ∈ c3.agent`
      \\ qmatch_assum_rename_tac`a2 ∈ c2.agent`
      \\ first_x_assum(qspec_then`a3`mp_tac)
      \\ simp[]
      \\ disch_then(mp_tac o Q.AP_TERM`decode_morphism c1 (swap c2)`)
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
      \\ simp[maps_to_in_chu, FUN_EQ_THM]
      \\ simp[is_chu_morphism_def]
      \\ simp[extensional_def]
      \\ fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
      \\ rw[]
      \\ metis_tac[] )
    \\ `g2 = g2'` by (
      simp[FUN_EQ_THM]
      \\ qx_gen_tac`p`
      \\ reverse(Cases_on`p ∈ pas c1.agent c3.agent`) >- fs[extensional_def]
      \\ fs[EXISTS_PROD]
      \\ qmatch_assum_rename_tac`a3 ∈ c3.agent`
      \\ qmatch_assum_rename_tac`a1 ∈ c1.agent`
      \\ first_x_assum(qspec_then`a3`mp_tac)
      \\ simp[]
      \\ disch_then(mp_tac o Q.AP_TERM`decode_morphism c1 (swap c2)`)
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
      \\ simp[maps_to_in_chu, FUN_EQ_THM]
      \\ asm_rewrite_tac[is_chu_morphism_def]
      \\ simp_tac(srw_ss())[]
      \\ simp_tac(srw_ss())[extensional_def]
      \\ rpt BasicProvers.VAR_EQ_TAC
      \\ simp_tac(srw_ss())[GSYM CONJ_ASSOC]
      \\ conj_tac >- fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
      \\ conj_tac >- fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
      \\ conj_tac >- metis_tac[]
      \\ conj_tac >- fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
      \\ conj_tac >- fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
      \\ conj_tac >- metis_tac[]
      \\ rw[]
      \\ metis_tac[] )
    \\ rw[])
  \\ `∀x. x ∈ (tensor_assoc_helper w c1 c2 c3).env ⇒ m x :- tensor c1 c2 → swap c3 -: chu w` suffices_by metis_tac[]
  \\ simp[tensor_assoc_helper_def, PULL_EXISTS]
  \\ simp[maps_to_in_chu, Abbr`m`]
  \\ simp[is_chu_morphism_def]
  \\ simp[extensional_def, PULL_EXISTS, EXISTS_PROD]
  \\ simp[Once tensor_def, hom_def]
  \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
  \\ simp[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
  \\ ntac 4 strip_tac
  \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
  \\ simp[Once (GSYM FORALL_AND_THM)]
  \\ qx_gen_tac`a3`
  \\ Cases_on`a3 ∈ c3.agent` \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`encode_morphism m`
  \\ `m :- c1 → swap c2 -: chu w`
  by (
    simp[Abbr`m`, maps_to_in_chu]
    \\ simp[is_chu_morphism_def]
    \\ simp[extensional_def] )
  \\ conj_asm1_tac >- metis_tac[]
  \\ simp[tensor_def, mk_cf_def, hom_def]
  \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
  \\ simp[Abbr`m`]
QED

Theorem homotopy_equiv_tensor_right:
  d ∈ chu_objects w ∧ c1 ≃ c2 -: w ⇒
  tensor c1 d ≃ tensor c2 d -: w
Proof
  rw[homotopy_equiv_def]
  \\ `c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w` by fs[maps_to_in_chu]
  \\ `c1.world = w ∧ c2.world = w` by fs[chu_objects_def]
  \\ qexists_tac`mk_chu_morphism (tensor c1 d) (tensor c2 d)
       <| map_agent := λp. encode_pair (f.map.map_agent (FST (decode_pair p)),
                                        SND (decode_pair p));
          map_env := λm. encode_morphism
            (decode_morphism c2 (swap d) m o f -: chu w) |>`
  \\ qexists_tac`mk_chu_morphism (tensor c2 d) (tensor c1 d)
       <| map_agent := λp. encode_pair (g.map.map_agent (FST (decode_pair p)),
                                        SND (decode_pair p));
          map_env := λm. encode_morphism
            (decode_morphism c1 (swap d) m o g -: chu w) |>`
  \\ qmatch_goalsub_abbrev_tac`h1 :- tensor c1 d → tensor c2 d -: _`
  \\ qmatch_goalsub_abbrev_tac`h2 :- tensor c2 d → tensor c1 d -: _`
  \\ ntac 2 (
    conj_asm1_tac
    >- (
      simp[maps_to_in_chu, Abbr`h1`, Abbr`h2`]
      \\ simp[is_chu_morphism_def]
      \\ simp[mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
      \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
      \\ conj_tac
      >- metis_tac[composable_maps_to, maps_to_composable,
                   is_category_chu, maps_to_in_def, maps_to_def,
                   decode_encode_chu_morphism]
      \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ conj_tac >- fs[maps_to_in_chu, is_chu_morphism_def]
      \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
      \\ rpt gen_tac \\ strip_tac
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
      \\ simp[Once tensor_def, mk_cf_def, hom_def]
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
      \\ conj_asm1_tac
      >- metis_tac[composable_maps_to, maps_to_composable,
                   is_category_chu, maps_to_in_def, maps_to_def]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ pop_assum kall_tac
      \\ simp[Once tensor_def, mk_cf_def, hom_def]
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
      \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ pop_assum kall_tac
      \\ DEP_REWRITE_TAC[compose_in_thm]
      \\ DEP_REWRITE_TAC[compose_thm]
      \\ DEP_REWRITE_TAC[chu_comp]
      \\ rewrite_tac[CONJ_ASSOC]
      \\ conj_tac >- metis_tac[maps_to_composable, composable_in_def]
      \\ simp[pre_chu_def, restrict_def]
      \\ reverse IF_CASES_TAC >- rfs[maps_to_in_chu]
      \\ fs[maps_to_in_chu, is_chu_morphism_def] ))
  \\ imp_res_tac maps_to_comp \\ fs[]
  \\ simp[homotopic_def, pre_chu_def]
  \\ fs[maps_to_in_chu]
  \\ simp[hom_comb_def]
  \\ simp[chu_id_morphism_map_def]
  \\ ntac 2 (qhdtm_x_assum`homotopic`mp_tac)
  \\ simp[homotopic_def, pre_chu_def]
  \\ simp[hom_comb_def, chu_id_morphism_map_def]
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ DEP_REWRITE_TAC[chu_comp]
  \\ simp[Once CONJ_ASSOC]
  \\ simp[Once CONJ_ASSOC]
  \\ conj_tac >- simp[composable_in_def, pre_chu_def]
  \\ simp[pre_chu_def]
  \\ simp[is_chu_morphism_def]
  \\ simp[restrict_def]
  \\ fs[is_chu_morphism_def]
  \\ simp[Abbr`h1`, Abbr`h2`, mk_chu_morphism_def]
  \\ simp[restrict_def]
  \\ simp[tensor_def, PULL_EXISTS, EXISTS_PROD, mk_cf_def, hom_def]
  \\ ntac 2 strip_tac
  \\ conj_tac \\ rpt gen_tac \\ strip_tac
  \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
  \\ (reverse IF_CASES_TAC >- metis_tac[])
  \\ pop_assum kall_tac
  \\ fs[maps_to_in_chu, is_chu_morphism_def]
  \\ metis_tac[]
QED

Theorem homotopy_equiv_tensor:
  c1 ≃ c2 -: w ∧ d1 ≃ d2 -: w ⇒
  tensor c1 d1 ≃ tensor c2 d2 -: w
Proof
  strip_tac
  \\ `c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧
      d1 ∈ chu_objects w ∧ d2 ∈ chu_objects w`
      by fs[homotopy_equiv_def, maps_to_in_chu]
  \\ PROVE_TAC[homotopy_equiv_trans, tensor_comm,
               iso_homotopy_equiv, homotopy_equiv_tensor_right]
QED

Theorem tensor_distrib:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ d ∈ chu_objects w ⇒
  tensor (sum c1 c2) d ≅ sum (tensor c1 d) (tensor c2 d) -: chu w
Proof
  strip_tac
  \\ `c1.world = w ∧ c2.world = w ∧ d.world = w` by fs[chu_objects_def]
  \\ simp[Once iso_objs_sym]
  \\ simp[iso_objs_thm]
  \\ qexists_tac`mk_chu_morphism (sum (tensor c1 d) (tensor c2 d))
                                 (tensor (sum c1 c2) d)
       <| map_agent := λa. sum_CASE (decode_sum a)
                             (λp. encode_pair (encode_sum (INL (FST (decode_pair p))),
                                               SND (decode_pair p)))
                             (λp. encode_pair (encode_sum (INR (FST (decode_pair p))),
                                               SND (decode_pair p)));
          map_env := λe.
            let m = decode_morphism (sum c1 c2) (swap d) e in
              encode_pair
                (encode_morphism (m o inj1 c1 c2 -: chu w),
                 encode_morphism (m o inj2 c1 c2 -: chu w)) |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[mk_chu_morphism_def]
    \\ simp[is_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_tac
    >- (
      simp[Once tensor_def, PULL_EXISTS, hom_def]
      \\ gen_tac \\ strip_tac
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
      \\ conj_asm1_tac >- rfs[sum_def]
      \\ qspecl_then[`chu w`,`inj1 c1 c2`,`x`]mp_tac maps_to_comp \\ simp[]
      \\ disch_then(first_assum o mp_then Any (qspec_then`c1`mp_tac))
      \\ simp[] \\ strip_tac
      \\ qspecl_then[`chu w`,`inj2 c1 c2`,`x`]mp_tac maps_to_comp \\ simp[]
      \\ disch_then(first_assum o mp_then Any (qspec_then`c2`mp_tac))
      \\ simp[] \\ strip_tac
      \\ simp[Once sum_def]
      \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
      \\ simp[Once tensor_def, PULL_EXISTS, hom_def] )
    \\ conj_tac
    >- (
      simp[Once sum_def, PULL_EXISTS]
      \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ gen_tac \\ strip_tac \\ simp[]
      \\ simp[Once tensor_def]
      \\ simp[Once sum_def] )
    \\ simp[Once sum_def, PULL_EXISTS]
    \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
    \\ rpt gen_tac
    \\ simp[CONJ_COMM]
    \\ simp[GSYM AND_IMP_INTRO]
    \\ strip_tac
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ conj_asm1_tac >- rfs[sum_def]
    \\ qspecl_then[`chu w`,`inj1 c1 c2`,`x`]mp_tac maps_to_comp \\ simp[]
    \\ disch_then(first_assum o mp_then Any (qspec_then`c1`mp_tac))
    \\ simp[] \\ strip_tac
    \\ qspecl_then[`chu w`,`inj2 c1 c2`,`x`]mp_tac maps_to_comp \\ simp[]
    \\ disch_then(first_assum o mp_then Any (qspec_then`c2`mp_tac))
    \\ simp[] \\ strip_tac
    \\ simp[Once sum_def, mk_cf_def]
    \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
    \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
    \\ simp[sum_eval_def]
    \\ strip_tac \\ simp[]
    \\ simp[Once tensor_def, mk_cf_def, hom_def]
    \\ (reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac)
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
    \\ simp[Once tensor_def, mk_cf_def, hom_def]
    \\ simp[Once sum_def]
    \\ (reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac)
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
    \\ simp[Once sum_def]
    \\ simp[mk_cf_def, PULL_EXISTS, EXISTS_PROD]
    \\ (reverse IF_CASES_TAC >- (
          fs[maps_to_in_chu, is_chu_morphism_def, sum_def, PULL_EXISTS, EXISTS_PROD]
          \\ metis_tac[] ))
    \\ simp[sum_eval_def]
    \\ DEP_REWRITE_TAC[compose_in_thm]
    \\ DEP_REWRITE_TAC[compose_thm]
    \\ DEP_REWRITE_TAC[chu_comp]
    \\ simp[CONJ_ASSOC]
    \\ (conj_tac >- (
      conj_asm2_tac >- fs[maps_to_in_chu]
      \\ irule maps_to_composable
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ metis_tac[inj_maps_to]))
    \\ simp[pre_chu_def, restrict_def]
    \\ fs[maps_to_in_chu]
    \\ simp[inj1_def, inj2_def, mk_chu_morphism_def]
    \\ simp[restrict_def, sum_def, PULL_EXISTS, EXISTS_PROD])
  \\ qmatch_goalsub_abbrev_tac`iso _ f`
  \\ simp[chu_iso_bij]
  \\ simp[Once CONJ_ASSOC]
  \\ reverse conj_tac >- fs[maps_to_in_chu]
  \\ conj_tac
  >- (
    simp[BIJ_IFF_INV]
    \\ conj_tac >- fs[maps_to_in_chu, is_chu_morphism_def]
    \\ qexists_tac`λp. sum_CASE (decode_sum (FST (decode_pair p)))
         (λx. encode_sum (INL (encode_pair (x, SND (decode_pair p)))))
         (λx. encode_sum (INR (encode_pair (x, SND (decode_pair p)))))`
    \\ simp[Abbr`f`, mk_chu_morphism_def, tensor_def, sum_def,
            PULL_EXISTS, EXISTS_PROD]
    \\ simp[restrict_def, PULL_EXISTS, EXISTS_PROD]
    \\ rw[] \\ simp[] \\ fs[] )
  \\ simp[BIJ_IFF_INV]
  \\ conj_tac >- fs[maps_to_in_chu, is_chu_morphism_def]
  \\ qexists_tac`λp. encode_morphism (@m.
        m :- (sum c1 c2) → (swap d) -: chu w ∧
        m o inj1 c1 c2 -: chu w = decode_morphism c1 (swap d) (FST (decode_pair p)) ∧
        m o inj2 c1 c2 -: chu w = decode_morphism c2 (swap d) (SND (decode_pair p)))`
  \\ simp[]
  \\ qho_match_abbrev_tac`(∀x. _ x ⇒ encode_morphism (m x) ∈ _) ∧ _`
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    simp[Abbr`f`, tensor_def, Once sum_def, PULL_EXISTS, EXISTS_PROD, hom_def]
    \\ rpt gen_tac \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`encode_morphism z = _`
    \\ qexists_tac`z` \\ simp[Abbr`z`]
    \\ simp[Abbr`m`]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
    \\ `(sum c1 c2).world = w` by simp[sum_def] \\ simp[]
    \\ SELECT_ELIM_TAC \\ simp[]
    \\ PROVE_TAC[sum_is_sum, EXISTS_UNIQUE_ALT] )
  \\ conj_tac
  >- (
    simp[Abbr`f`]
    \\ simp[mk_chu_morphism_def]
    \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
    \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
    \\ simp[restrict_def]
    \\ gen_tac \\ strip_tac
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ conj_asm1_tac >- rfs[sum_def]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ simp[Abbr`m`]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ conj_asm1_tac
    >- (
      conj_tac \\ irule composable_maps_to \\ simp[]
      \\ (conj_tac >- fs[maps_to_in_chu])
      \\ irule maps_to_composable
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ metis_tac[inj_maps_to] )
    \\ AP_TERM_TAC
    \\ SELECT_ELIM_TAC
    \\ PROVE_TAC[sum_is_sum, EXISTS_UNIQUE_ALT] )
  \\ simp[Abbr`f`]
  \\ simp[mk_chu_morphism_def]
  \\ simp[Once sum_def, PULL_EXISTS, EXISTS_PROD]
  \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
  \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
  \\ simp[restrict_def]
  \\ rpt gen_tac \\ strip_tac
  \\ simp[Once tensor_def, hom_def, PULL_EXISTS]
  \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
  \\ conj_asm1_tac >- (
    simp[Abbr`m`]
    \\ SELECT_ELIM_TAC
    \\ simp[]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ PROVE_TAC[sum_is_sum, EXISTS_UNIQUE_ALT] )
  \\ reverse IF_CASES_TAC >- (rfs[sum_def] \\ metis_tac[])
  \\ pop_assum kall_tac
  \\ simp[Abbr`m`]
  \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
  \\ simp[]
  \\ SELECT_ELIM_TAC
  \\ PROVE_TAC[sum_is_sum, EXISTS_UNIQUE_ALT]
QED

Theorem tensor_overlap:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ∧
  ¬DISJOINT (ensure c) (prevent d) ⇒
  tensor c d ≃ cfT w -: w
Proof
  strip_tac
  \\ irule empty_env_nonempty_agent
  \\ simp[]
  \\ fs[IN_DISJOINT]
  \\ simp[Once tensor_def]
  \\ fs[ensure_def, prevent_def]
  \\ simp[CROSS_EMPTY_EQN]
  \\ simp[GSYM MEMBER_NOT_EMPTY]
  \\ conj_tac >- metis_tac[]
  \\ simp[tensor_def, hom_def, EXTENSION]
  \\ `c.world = w ∧ d.world = w` by fs[chu_objects_def]
  \\ simp[maps_to_in_chu]
  \\ simp[is_chu_morphism_def]
  \\ metis_tac[]
QED

Theorem tensor_self:
  c ∈ chu_objects w ∧ ctrl c ≠ ∅ ⇒
  tensor c c ≃ cfT w -: w
Proof
  strip_tac
  \\ irule tensor_overlap
  \\ fs[ctrl_def, DISJOINT_DEF]
QED

(* TODO: examples re tensor being relative to a coarse world model *)

Definition par_def:
  par c d = mk_cf <| world := c.world ∪ d.world;
    agent := IMAGE encode_morphism (chu c.world | swap c → d |);
    env := IMAGE encode_pair (c.env × d.env);
    eval := λa e.
      c.eval ((decode_morphism (swap c) d a).map.map_env (SND (decode_pair e)))
             (FST (decode_pair e)) |>
End

Theorem swap_tensor_par:
  swap (tensor (swap c) (swap d)) = par c d
Proof
  rw[par_def, tensor_def, cf_component_equality]
  \\ rw[mk_cf_def, swap_def, FUN_EQ_THM]
  \\ rw[]
  \\ metis_tac[]
QED

Theorem par_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ⇒ par c d ∈ chu_objects w
Proof
  rw[GSYM swap_tensor_par]
QED

Theorem par_comm:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ⇒
  par c d ≅ par d c -: chu w
Proof
  rw[GSYM swap_tensor_par]
  \\ irule tensor_comm
  \\ simp[]
QED

Theorem par_assoc:
  c1 ∈ chu_objects w ∧
  c2 ∈ chu_objects w ∧
  c3 ∈ chu_objects w ⇒
  par c1 (par c2 c3) ≅ par (par c1 c2) c3 -: chu w
Proof
  rw[GSYM swap_tensor_par]
  \\ irule tensor_assoc
  \\ simp[]
QED

Theorem par_cfbot[simp]:
  c ∈ chu_objects w ⇒
  par c (cfbot w w) ≅ c -: chu w ∧
  par (cfbot w w) c ≅ c -: chu w
Proof
  rw[GSYM swap_tensor_par, cfbot_def]
  \\ metis_tac[tensor_cf1, swap_swap, swap_in_chu_objects, swap_iso]
QED

Theorem homotopy_equiv_par:
  c1 ≃ c2 -: w ∧
  d1 ≃ d2 -: w ⇒
  par c1 d1 ≃ par c2 d2 -: w
Proof
  rw[GSYM swap_tensor_par]
  \\ DEP_REWRITE_TAC[homotopy_equiv_swap]
  \\ DEP_REWRITE_TAC[tensor_in_chu_objects]
  \\ simp[]
  \\ conj_asm1_tac >- fs[homotopy_equiv_def, maps_to_in_chu]
  \\ irule homotopy_equiv_tensor
  \\ simp[]
QED

Theorem par_distrib:
  c1 ∈ chu_objects w ∧
  c2 ∈ chu_objects w ∧
  d ∈ chu_objects w ⇒
  par (c1 && c2) d ≅ par c1 d && par c2 d -: chu w
Proof
  rw[GSYM swap_tensor_par]
  \\ rw[GSYM swap_sum_prod]
  \\ irule tensor_distrib
  \\ rw[]
QED

Definition lollipop_def:
  lollipop c d = mk_cf
    <| world := c.world ∪ d.world;
       agent := IMAGE encode_morphism (chu c.world | c → d |);
       env := IMAGE encode_pair (c.agent × d.env);
       eval := λa e.
         c.eval (FST (decode_pair e))
           ((decode_morphism c d a).map.map_env (SND (decode_pair e))) |>
End

Theorem lollipop_eq_par:
  lollipop c d = par (swap c) d
Proof
  rw[lollipop_def, par_def]
QED

Theorem cf1_lollipop[simp]:
  c ∈ chu_objects w ⇒
  lollipop (cf1 w w) c ≅ c -: chu w
Proof
  rw[lollipop_eq_par]
  \\ rw[GSYM cfbot_def]
QED

Theorem lollipop_cfbot[simp]:
  c ∈ chu_objects w ⇒
  lollipop c (cfbot w w) ≅ swap c -: chu w
Proof
  rw[lollipop_eq_par]
QED

val _ = export_theory();
