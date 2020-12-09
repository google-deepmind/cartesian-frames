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
  pred_setTheory
  cf0Theory matrixTheory matrixLib cf2Theory cf4Theory

val _ = new_theory"ex4";

Definition prime_env_def:
  prime_env = {"P"; "N"}
End

Definition prime_agent_sensitive_def:
  prime_agent_sensitive = {"A"; "I"}
End

Definition prime_agent_coarse_def:
  prime_agent_coarse = prime_env ∪ prime_agent_sensitive
End

Theorem prime_agent_coarse_eq = CONV_RULE(RAND_CONV EVAL) prime_agent_coarse_def

Definition prime_agent_fine_def:
  prime_agent_fine = IMAGE (UNCURRY(++)) (prime_agent_coarse × {"H"; "C"}) DIFF {"AC"; "IC"}
End

Theorem prime_agent_fine_eq = CONV_RULE(RAND_CONV EVAL) prime_agent_fine_def

Definition prime_world_def:
  prime_world = IMAGE (λ(x,y,z). x ++ y++ z) (prime_env × prime_agent_sensitive × {"H"; "C"})
End

Theorem prime_world_eq = CONV_RULE(RAND_CONV EVAL) prime_world_def

Definition prime_cf_def:
  prime_cf = mk_cf <|
    world := prime_world;
    agent := prime_agent_fine;
    env := prime_env;
    eval := λa e. e ++ (if e = TAKE 1 a then "A" else
                        if TAKE 1 a ∈ {"P"; "N"} then "I"
                        else TAKE 1 a) ++ (DROP 1 a) |>
End

Theorem wf_prime_cf[simp]:
  wf prime_cf
Proof
  EVAL_TAC \\ rw[] \\ EVAL_TAC \\ pop_assum mp_tac \\ EVAL_TAC
QED

Definition prime_world_coarse_def:
  prime_world_coarse = IMAGE (TAKE 2) prime_world
End

Theorem prime_world_coarse_eq = CONV_RULE(RAND_CONV EVAL) prime_world_coarse_def

Theorem move_prime_cf_matrix:
  cf_matrix (move (TAKE 2) prime_world_coarse prime_cf) =
             (* N *) (* P *)
    (* AH *) [["NA"; "PA"];
    (* IH *)  ["NI"; "PI"];
    (* NC *)  ["NA"; "PI"];
    (* NH *)  ["NA"; "PI"];
    (* PC *)  ["NI"; "PA"];
    (* PH *)  ["NI"; "PA"]]
Proof
  simp[cf_matrix_def]
  \\ simp[EVAL``prime_cf.env``, EVAL``prime_cf.agent``]
  \\ qsort_set_to_list_tac
  \\ EVAL_TAC
QED

Theorem biextensional_collapse_move_prime_cf_matrix:
  cf_matrix (biextensional_collapse (move (TAKE 2) prime_world_coarse prime_cf)) =
            (* N *) (* P *)
    (* A *) [["NA"; "PA"];
    (* I *)  ["NI"; "PI"];
    (* N *)  ["NA"; "PI"];
    (* P *)  ["NI"; "PA"]]
Proof
  rw[biextensional_collapse_def]
  \\ simp[EVAL``prime_cf.env``, EVAL``prime_cf.agent``]
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "PH"; "PC"}`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ `FINITE s ∧ s ≠ ∅` by simp[]
  \\ simp[rep_HD_QSORT_SET_TO_LIST]
  \\ rpt(pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "PH"; "PC"}`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ `FINITE s ∧ s ≠ ∅` by simp[]
  \\ simp[rep_HD_QSORT_SET_TO_LIST]
  \\ rpt(pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "NH"; "NC"}`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ `FINITE s ∧ s ≠ ∅` by simp[]
  \\ simp[rep_HD_QSORT_SET_TO_LIST]
  \\ rpt(pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "NH"; "NC"}`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ `FINITE s ∧ s ≠ ∅` by simp[]
  \\ simp[rep_HD_QSORT_SET_TO_LIST]
  \\ rpt(pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "AH" }`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ simp[]
  \\ rpt(pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "IH" }`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ simp[]
  \\ rpt(pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "P" }`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ simp[]
  \\ rpt(pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "N" }`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ simp[]
  \\ rpt(pop_assum kall_tac)
  \\ qsort_set_to_list_tac
  \\ CONV_TAC(PATH_CONV"lrrrrl"EVAL)
  \\ rw[cf_matrix_def]
  \\ qsort_set_to_list_tac
  \\ EVAL_TAC
QED

(* TODO: observable set in move but not in base *)

(* TODO: move as a product *)

val _ = export_theory();
