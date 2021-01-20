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

open HolKernel boolLib bossLib boolSimps Parse dep_rewrite
  pred_setTheory listTheory sortingTheory categoryTheory
  matrixLib matrixTheory
  cf0Theory cf1Theory cf2Theory cf5Theory cf6Theory cf7Theory
  ex1Theory

val _ = new_theory"ex7";

Definition pd_def:
  pd = mk_cf <| world := {"0"; "1"; "2"; "3"};
                agent := {"c"; "d"};
                env := {"c"; "d"};
                eval := λa b.
                  if a = b then
                    if a = "c" then "2" else "1"
                  else if a = "c" then "0" else "3" |>
End

Theorem cf_matrix_pd:
  cf_matrix pd =
    [["2"; "0"];
     ["3"; "1"]]
Proof
  rw[pd_def, cf_matrix_def, mk_cf_def]
  \\ qsort_set_to_list_tac
  \\ EVAL_TAC
QED

Definition ac_def:
  ac = mk_cf (pd with agent := {"c"})
End

Definition ad_def:
  ad = mk_cf (pd with agent := {"d"})
End

Theorem cf_matrix_ac:
  cf_matrix ac = [["2"; "0"]]
Proof
  rw[ac_def, pd_def, cf_matrix_def, mk_cf_def]
  \\ qsort_set_to_list_tac
  \\ EVAL_TAC
  \\ qexists_tac`"c"` \\ simp[]
QED

Theorem cf_matrix_ad:
  cf_matrix ad = [["3"; "1"]]
Proof
  rw[ad_def, pd_def, cf_matrix_def, mk_cf_def]
  \\ qsort_set_to_list_tac
  \\ EVAL_TAC
  \\ qexists_tac`"d"` \\ simp[]
QED

Theorem cf_matrix_ac_sum_ad:
  ∃p. p PERMUTES count (CARD (sum ac ad).env) ∧
  cf_matrix (sum ac ad) = permute_cols p
    [["2"; "0"; "2"; "0"];
     ["3"; "1"; "1"; "3"]]
Proof
  rw[cf_matrix_def, sum_def]
  \\ rw[EVAL``ac.env``] \\ rw[EVAL``ad.env``]
  \\ rw[EVAL``ac.agent``] \\ rw[EVAL``ad.agent``]
  \\ rw[EVAL``ac.world``] \\ rw[EVAL``ad.world``]
  \\ CONV_TAC(ONCE_DEPTH_CONV(fn tm =>
    if pred_setSyntax.is_image tm orelse
       pred_setSyntax.is_union tm then
    EVAL tm else NO_CONV tm))
  \\ qsort_set_to_list_tac
  \\ qexists_tac`λn. if n = 1 then 2 else
                     if n = 2 then 3 else
                     if n = 3 then 1 else n`
  \\ EVAL_TAC
  \\ rw[BIJ_IFF_INV]
  \\ qexists_tac`λn. if n = 1 then 3 else
                     if n = 2 then 1 else
                     if n = 3 then 2 else n`
  \\ rw[]
QED

Definition uc_def:
  uc = mk_cf <| world := {"0"; "1"};
                agent := {"p"; "s"};
                env := {"p"; "s"};
                eval := λa e. if a = "s" ∧ e = "s"
                              then "1" else "0" |>
End

Theorem cf_matrix_uc:
  cf_matrix uc = [["0"; "0"]; ["0"; "1"]]
Proof
  rw[cf_matrix_def, uc_def]
  \\ qsort_set_to_list_tac
  \\ EVAL_TAC
QED

Theorem swap_uc:
  swap uc = uc
Proof
  rw[swap_def, uc_def, cf_component_equality]
  \\ rw[mk_cf_def, FUN_EQ_THM]
  \\ rw[]
QED

Theorem uc_in_chu_objects:
  uc ∈ chu_objects uc.world
Proof
  rw[chu_objects_def]
  \\ rw[uc_def]
  \\ EVAL_TAC
  \\ rw[SUBSET_DEF]
QED

Definition pp_def:
  pp = mk_chu_morphism uc uc
         <| map_agent := K "p"; map_env := K "p" |>
End

Theorem pp_maps_to:
  pp :- uc → uc -: chu uc.world
Proof
  rw[maps_to_in_chu, uc_in_chu_objects]
  \\ rw[pp_def]
  \\ rw[is_chu_morphism_def, mk_chu_morphism_def]
  \\ rpt (pop_assum mp_tac)
  \\ EVAL_TAC \\ rw[]
QED

Theorem hom_uc:
  (chu uc.world |uc → uc|) = { id uc -: chu uc.world; pp }
Proof
  reverse(rw[hom_def, SET_EQ_SUBSET])
  >- simp[pp_maps_to]
  >- ( irule id_maps_to \\ simp[uc_in_chu_objects] )
  \\ rw[SUBSET_DEF, maps_to_in_chu]
  \\ fs[is_chu_morphism_def]
  \\ rw[morphism_component_equality]
  \\ simp[chu_morphism_map_component_equality]
  \\ simp[chu_id_morphism_map_def, pp_def, mk_chu_morphism_def]
  \\ simp[restrict_def, FUN_EQ_THM]
  \\ fs[extensional_def]
  \\ `uc.agent = uc.env` by EVAL_TAC \\ gs[]
  \\ simp[GSYM FORALL_AND_THM]
  \\ qmatch_goalsub_abbrev_tac`P ∨ _`
  \\ Cases_on`P = T` \\ simp[Abbr`P`]
  \\ disj2_tac
  \\ qx_gen_tac`a`
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ qpat_x_assum`_ ≠ T`mp_tac
  \\ simp[]
  \\ disch_then(qx_choose_then`b`mp_tac)
  \\ Cases_on`b ∈ uc.env` \\ simp[]
  \\ `∀x. x ∈ uc.env ⇔ (x = "s" ∨ x = "p")`
     by (EVAL_TAC \\ simp[] \\ metis_tac[])
  \\ `∀x y. x ∈ uc.env ∧ y ∈ uc.env ⇒
            (uc.eval x y = if x = "s" ∧ y = "s" then "1" else "0")`
     by ( simp[] \\ EVAL_TAC \\ rw[] )
  \\ metis_tac[EVAL``"s"="p"``, EVAL``"1"="0"``]
QED

Theorem cf_matrix_uc_tensor_uc:
  ∃p. p PERMUTES count 2 ∧
  cf_matrix (tensor uc uc) =
    permute_cols p
      [["0"; "0"];
       ["0"; "0"];
       ["0"; "0"];
       ["1"; "0"]]
Proof
  rw[tensor_def, cf_matrix_def]
  \\ simp[swap_uc, hom_uc]
  \\ CONV_TAC(ONCE_DEPTH_CONV(fn tm =>
    if pred_setSyntax.is_image tm then
    EVAL tm else NO_CONV tm))
  \\ qsort_set_to_list_tac
  \\ IF_CASES_TAC
  >- (
    `id uc -:chu uc.world = pp` by
      metis_tac[id_maps_to, decode_encode_chu_morphism, pp_maps_to,
      is_category_chu, chu_obj, uc_in_chu_objects]
    \\ `F` suffices_by rw[]
    \\ pop_assum mp_tac
    \\ simp[morphism_component_equality, chu_morphism_map_component_equality, pp_def, uc_in_chu_objects]
    \\ simp[mk_chu_morphism_def, FUN_EQ_THM, restrict_def, chu_id_morphism_map_def]
    \\ disj1_tac
    \\ qexists_tac`"s"`
    \\ EVAL_TAC )
  \\ CONV_TAC(PATH_CONV"brrr"EVAL)
  \\ qmatch_goalsub_abbrev_tac`QSORT R [m1; m2]`
  \\ `decode_morphism uc uc m1 = id uc -:chu uc.world ∧
      decode_morphism uc uc m2 = pp`
    by metis_tac[decode_encode_chu_morphism, id_maps_to, pp_maps_to,
                 is_category_chu, chu_obj, uc_in_chu_objects]
  \\ `PERM [m1; m2] (QSORT R [m1; m2])` by metis_tac[QSORT_PERM]
  \\ pop_assum mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())
       [PERM_CONS_EQ_APPEND, APPEND_EQ_SING]))
  \\ strip_tac \\ gs[mk_cf_def]
  \\ simp[uc_in_chu_objects]
  \\ CONV_TAC(PATH_CONV"brr"EVAL)
  \\ TRY (
    qexists_tac`λn. 1 - n`
    \\ reverse conj_tac >- EVAL_TAC
    \\ simp[BIJ_IFF_INV]
    \\ qexists_tac`λn. 1 - n`
    \\ rw[] )
  \\ qexists_tac`I`
  \\ reverse conj_tac >- EVAL_TAC
  \\ metis_tac[BIJ_ID, combinTheory.I_THM]
QED

(* TODO: subsums and subtensors of these examples *)

Theorem no_subtensors:
  ∃c d w.
    c ∈ chu_objects w ∧ d ∈ chu_objects w ∧
    ∀t. ¬is_subtensor c d t
Proof
  qexists_tac`test_yesterday`
  \\ qexists_tac`swap test_demanding`
  \\ qexists_tac`test_world`
  \\ simp[]
  \\ rw[is_subtensor_def]
  \\ qmatch_goalsub_abbrev_tac`tensor c d`
  \\ `(tensor c d).env = ∅`
  by (
    rw[tensor_def]
    \\ rw[Abbr`c`, Abbr`d`, hom_def, EXTENSION]
    \\ rw[maps_to_in_chu]
    \\ metis_tac[no_morphisms_yesterday_demanding] )
  \\ simp[]
  \\ CCONTR_TAC \\ gs[restrict_def]
  \\ fs[homotopy_equiv_def]
  \\ fs[maps_to_in_chu]
  \\ fs[is_chu_morphism_def]
  \\ qpat_x_assum`∀e. e ∉ c.env`mp_tac
  \\ simp[Abbr`c`]
  \\ EVAL_TAC
  \\ simp[]
  \\ metis_tac[]
QED

val _ = export_theory();
