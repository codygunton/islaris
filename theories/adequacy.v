(****************************************************************************)
(* BSD 2-Clause License                                                     *)
(*                                                                          *)
(* Copyright (c) 2019-2021 The Islaris Developers                           *)
(*                                                                          *)
(* Michael Sammler                                                          *)
(* Rodolphe Lepigre                                                         *)
(* Angus Hammond                                                            *)
(* Brian Campbell                                                           *)
(* Jean Pichon-Pharabod                                                     *)
(* Peter Sewell                                                             *)
(*                                                                          *)
(* All rights reserved.                                                     *)
(*                                                                          *)
(* This research was supported in part by a European Research Council       *)
(* (ERC) Consolidator Grant for the project "RustBelt", funded under        *)
(* the European Union's Horizon 2020 Framework Programme (grant agreement   *)
(* no. 683289), in part by a European Research Council (ERC) Advanced       *)
(* Grant "ELVER" under the European Union's Horizon 2020 research and       *)
(* innovation programme (grant agreement no. 789108), in part by the UK     *)
(* Government Industrial Strategy Challenge Fund (ISCF) under the Digital   *)
(* Security by Design (DSbD) Programme, to deliver a DSbDtech enabled       *)
(* digital platform (grant 105694), in part by a Google PhD Fellowship      *)
(* (Sammler), in part by an EPSRC Doctoral Training studentship             *)
(* (Hammond), and in part by awards from Android Security's ASPIRE          *)
(* program and from Google Research.                                        *)
(*                                                                          *)
(*                                                                          *)
(* Redistribution and use in source and binary forms, with or without       *)
(* modification, are permitted provided that the following conditions are   *)
(* met:                                                                     *)
(*                                                                          *)
(* 1. Redistributions of source code must retain the above copyright        *)
(* notice, this list of conditions and the following disclaimer.            *)
(*                                                                          *)
(* 2. Redistributions in binary form must reproduce the above copyright     *)
(* notice, this list of conditions and the following disclaimer in the      *)
(* documentation and/or other materials provided with the distribution.     *)
(*                                                                          *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS      *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT        *)
(* LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR    *)
(* A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT     *)
(* HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,   *)
(* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT         *)
(* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,    *)
(* DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY    *)
(* THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT      *)
(* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE    *)
(* OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.     *)
(*                                                                          *)
(*                                                                          *)
(* Exceptions to this license are detailed in THIRD_PARTY_FILES.md          *)
(****************************************************************************)

From iris.proofmode Require Import tactics.
From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra Require Import csum excl auth cmra_big_op gmap dfrac_agree.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From isla Require Export ghost_state lifting.
Set Default Proof Using "Type".

Class islaPreG Σ := PreIslaG {
  isla_pre_invG :: invGpreS Σ;
  heap_pre_instrs_inG :: inG Σ (instrtblUR);
  heap_pre_regs_inG :: ghost_mapG Σ string valu;
  heap_pre_struct_regs_inG :: ghost_mapG Σ (string * string) valu;
  heap_pre_mem_inG :: ghost_mapG Σ addr byte;
  heap_pre_backed_mem_inG :: inG Σ (backed_memUR);
  heap_pre_spec_inG :: inG Σ (dfrac_agreeR specO);
  heap_pre_charged_inG :: inG Σ chargedUR;
  heap_pre_budget_inG :: inG Σ budgetUR;
}.

Definition islaΣ : gFunctors :=
  #[invΣ; GFunctor (constRF instrtblUR);
   ghost_mapΣ string valu;
   ghost_mapΣ (string * string) valu;
   ghost_mapΣ addr byte;
   GFunctor (constRF backed_memUR);
   GFunctor (dfrac_agreeR specO);
   GFunctor (constRF chargedUR);
   GFunctor (constRF budgetUR)].

Global Instance subG_islaPreG {Σ} : subG islaΣ Σ → islaPreG Σ.
Proof. solve_inG. Qed.

Definition initial_local_state `{!Arch} (regs : reg_map) : seq_local_state := {|
  seq_trace := tnil;
  seq_regs := regs;
  seq_pc_reg := arch_pc_reg;
  seq_nb_state := false;
|}.

(** Adequacy with step budgets: the instructions at the addresses in
[charged] are charged, the program starts with [step_credits budget], and
every run performs at most [budget] fetches of charged instructions. *)
Lemma isla_budget_adequacy Σ `{!Arch} `{!islaPreG Σ} (instrs : gmap addr isla_trace) (mem : mem_map) (regs : list reg_map) (Pκs : spec) (charged : gset addr) (budget : nat) t2 σ2 κs n:
  Pκs [] →
  (∀ {HG : islaG Σ},
    ⊢ instr_table_raw instrs -∗ charged_set charged -∗ step_credits budget -∗
      backed_mem (dom mem) -∗ spec_trace Pκs -∗ ([∗ map] a↦b∈mem, bv_unsigned a ↦ₘ b)
    ={⊤}=∗ [∗ list] rs ∈ regs, ∀ (_ : threadG), ([∗ map] r↦v∈rs, r ↦ᵣ v) -∗ WPasm tnil) →
  nsteps n (initial_local_state <$> regs, {| seq_instrs := instrs; seq_mem := mem; seq_charged := charged; seq_fetches := 0 |}) κs (t2, σ2) →
  (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧ Pκs κs ∧ (σ2.(seq_fetches) ≤ budget)%nat.
Proof.
  move => ? Hwp.
  apply: wp_strong_adequacy => ?.
  set i := to_instrtbl instrs.
  set bm := to_backed_mem (dom mem).
  iMod (own_alloc (i)) as (γi) "#Hi" => //.
  iMod (own_alloc (bm)) as (γbm) "#Hb" => //.
  iMod (own_alloc (to_agree (charged : leibnizO (gset addr)) : chargedUR)) as (γc) "#Hc" => //.
  iMod (own_alloc ((● (budget : natUR) ⋅ ◯ (budget : natUR)) : budgetUR)) as (γb) "[Hba Hbf]".
  { by apply auth_both_valid_discrete. }
  iMod (own_alloc (to_frac_agree (A:= _ -d> _) (1/2 + 1/2) Pκs)) as (γs) "Hs" => //.
  rewrite frac_agree_op. iDestruct "Hs" as "[Hs1 Hs2]".
  iMod (ghost_map_alloc mem) as (γm) "[Hm1 Hm2]".

  set (HheapG := HeapG _ _ γi _ _ _ γm _ γbm κs Pκs _ γs _ γc _ γb budget).
  set (HislaG := IslaG _ _ HheapG).
  iAssert (instr_table_raw instrs) as "#His". { by rewrite instr_table_raw_eq. }
  iAssert (charged_set charged) as "#Hcs". { by rewrite charged_set_eq. }
  iAssert (step_credits budget) with "[Hbf]" as "Hcred". { by rewrite step_credits_eq. }
  iAssert (backed_mem (dom mem)) as "#Hbm". { by rewrite backed_mem_eq. }

  iMod (Hwp HislaG with "His Hcs Hcred Hbm [Hs1] [Hm2]") as "Hwp". {
    rewrite spec_trace_eq. iExists _. rewrite spec_trace_raw_eq. by iFrame.
  } {
    iApply (big_sepM_impl with "Hm2"). iIntros "!>" (a b ?) "Ha".
    iApply mem_mapsto_byte_to_mapsto. rewrite mem_mapsto_byte_eq.
    iExists _. iFrame. by rewrite Z_to_bv_checked_bv_unsigned.
  }
  iModIntro.
  iExists _, (replicate (length regs) (λ _, True%I)), _, _.
  iSplitL "Hs2 Hm1 Hba"; last first; [iSplitL|].
  - rewrite big_sepL2_replicate_r ?length_fmap // big_sepL_fmap.
    iApply (big_sepL_impl with "Hwp").
    iIntros "!>" (? rs ?) "Hwp".
    iMod (ghost_map_alloc (rs)) as (γr) "[Hr1 Hr2]".
    iMod (ghost_map_alloc (∅ : gmap (string * string) valu)) as (γsr) "[Hsr1 Hsr2]".
    set (HthreadG := ThreadG γr γsr).
    setoid_rewrite wp_asm_unfold.
    iApply ("Hwp" with "[Hr2]"); [|done..|].
    + iApply (big_sepM_impl with "Hr2").
      iIntros "!>" (???) "?". by rewrite reg_mapsto_eq.
    + iExists _, _. iFrame. iPureIntro. split_and! => //.
      * move => /=. naive_solver.
      * move => ?? [?[??]]. simplify_map_eq.
  - iIntros (?????) "(Hspec&_&_&_&Hbud) ? ?".
    iDestruct (budget_bound with "Hbud") as %Hbound.
    iApply fupd_mask_intro; [done|]. iIntros "_".
    iDestruct "Hspec" as (Pκs' ? Hκs Hspec ?) "?".
    simpl in *. subst.
    iPureIntro. split; [naive_solver|]. split; [|done].
    by rewrite right_id_L.
  - simpl. iFrame "His Hbm Hcs Hm1". iSplitL "Hs2".
    { iExists _, [] => /=. rewrite spec_trace_raw_eq. by iFrame. }
    iExists budget. iFrame "Hba". iPureIntro. simpl. lia.
Qed.

Lemma isla_adequacy Σ `{!Arch} `{!islaPreG Σ} (instrs : gmap addr isla_trace) (mem : mem_map) (regs : list reg_map) (Pκs : spec) t2 σ2 κs n:
  Pκs [] →
  (∀ {HG : islaG Σ},
    ⊢ instr_table instrs -∗ backed_mem (dom mem) -∗ spec_trace Pκs -∗ ([∗ map] a↦b∈mem, bv_unsigned a ↦ₘ b)
    ={⊤}=∗ [∗ list] rs ∈ regs, ∀ (_ : threadG), ([∗ map] r↦v∈rs, r ↦ᵣ v) -∗ WPasm tnil) →
  nsteps n (initial_local_state <$> regs, {| seq_instrs := instrs; seq_mem := mem; seq_charged := ∅; seq_fetches := 0 |}) κs (t2, σ2) →
  (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧ Pκs κs.
Proof.
  move => ? Hwp Hsteps.
  have [? [? _]] : (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧ Pκs κs ∧ (σ2.(seq_fetches) ≤ 0)%nat.
  { apply: (isla_budget_adequacy Σ instrs mem regs Pκs ∅ 0); [done| |done].
    iIntros (?) "Hi Hc _ Hbm Hspec Hmem".
    iApply (Hwp with "[Hi Hc] Hbm Hspec Hmem").
    rewrite instr_table_eq /instr_table_def. iFrame. }
  done.
Qed.

(** * Bound on the number of steps *)
(** Every step inside an instruction strictly shortens its trace, so when
every instruction is charged, the number of steps of a run is bounded by the
number of fetches times the longest trace. *)

Local Open Scope nat_scope.

Lemma subst_trace_length v x t :
  isla_trace_length (subst_trace v x t) = isla_trace_length t.
Proof.
  revert t. fix IH 1. intros [|e t'|ts]; simpl; [done|by rewrite IH|].
  f_equal. revert ts. fix IHts 1. intros [|t ts]; [done|].
  rewrite !fmap_cons /= IH IHts. done.
Qed.

Lemma isla_trace_length_elem_of es ts :
  es ∈ ts → isla_trace_length es ≤ sum_list (isla_trace_length <$> ts).
Proof.
  induction ts as [|t ts IH]; [by intros ?%elem_of_nil|].
  move => /elem_of_cons [->|/IH ?]; rewrite fmap_cons /=; lia.
Qed.

Lemma trace_step_length t regs κ t' :
  trace_step t regs κ t' →
  (∀ es, κ ≠ Some (LDone es)) →
  isla_trace_length t' < isla_trace_length t.
Proof.
  move => Hstep Hκ. inversion Hstep; subst; simpl; rewrite ?subst_trace_length; try lia.
  - opose proof (isla_trace_length_elem_of _ _ _); [done|]. lia.
  - naive_solver.
Qed.

Definition max_trace_length (instrs : gmap addr isla_trace) : nat :=
  max_list ((λ p, isla_trace_length p.2) <$> map_to_list instrs).

Lemma max_trace_length_lookup instrs a t :
  instrs !! a = Some t → isla_trace_length t ≤ max_trace_length instrs.
Proof.
  move => ?. apply max_list_elem_of_le, elem_of_list_fmap.
  exists (a, t). split; [done|]. by apply elem_of_map_to_list.
Qed.

Lemma seq_step_progress θ σ κ θ' σ' efs :
  seq_step θ σ κ θ' σ' efs →
  σ.(seq_charged) = dom σ.(seq_instrs) →
  efs = [] ∧ σ'.(seq_instrs) = σ.(seq_instrs) ∧ σ'.(seq_charged) = σ.(seq_charged) ∧
  θ.(seq_nb_state) = false ∧
  (θ'.(seq_nb_state) = true ∧ σ'.(seq_fetches) = σ.(seq_fetches) ∨
   θ'.(seq_nb_state) = false ∧
     isla_trace_length θ'.(seq_trace) < isla_trace_length θ.(seq_trace) ∧
     σ'.(seq_fetches) = σ.(seq_fetches) ∨
   θ'.(seq_nb_state) = false ∧
     isla_trace_length θ'.(seq_trace) ≤ max_trace_length σ.(seq_instrs) ∧
     σ'.(seq_fetches) = S σ.(seq_fetches)).
Proof.
  inversion 1 as [?? κ0 t' κ' ?? Hnb Hts Hm]; subst => Hch.
  destruct κ0 as [[| | | | | | es | | |]|]; simpl in Hm.
  7: {
    destruct Hm as (pc & Hpc & Hm). inversion Hts; subst.
    destruct (seq_instrs σ !! pc) as [es'|] eqn:Hl; destruct_and!; subst; simpl.
    + rewrite decide_True; [|rewrite Hch; by apply: elem_of_dom_2].
      split_and!; [done..|]. right; right. split_and!; [done| |done].
      by apply: max_trace_length_lookup.
    + split_and!; [done..|]. by left. }
  all: have Hlt := trace_step_length _ _ _ _ Hts ltac:(naive_solver).
  all: repeat match goal with H : ∃ _, _ |- _ => destruct H end;
    destruct_and?; repeat case_match; destruct_and?; destruct_or?; destruct_and?;
    subst; simpl in *; try naive_solver lia.
  (* [LAssert b]: the thread stops iff [b] is false. *)
  destruct b; naive_solver lia.
Qed.

Lemma fetches_bound_steps_aux n θ σ κs t2 σ2 :
  nsteps n ([θ], σ) κs (t2, σ2) →
  σ.(seq_charged) = dom σ.(seq_instrs) →
  σ.(seq_fetches) ≤ σ2.(seq_fetches) ∧
  (θ.(seq_nb_state) = true → n = 0) ∧
  (θ.(seq_nb_state) = false →
   n + σ.(seq_fetches) * S (max_trace_length σ.(seq_instrs)) ≤
   isla_trace_length θ.(seq_trace) + 1 + σ2.(seq_fetches) * S (max_trace_length σ.(seq_instrs))).
Proof.
  move Hρ: ([θ], σ) => ρ Hsteps. move Hρ2: (t2, σ2) => ρ2 in Hsteps.
  elim: Hsteps θ σ Hρ Hρ2 => {n ρ ρ2 κs} [ρ|n ρ1 ρ2 ρ3 κ κs Hstep Hsteps IH] θ σ ? ? Hch; subst.
  - simplify_eq. split_and!; [done|done|lia].
  - inversion Hstep as [e1 σ1' e2 σ2' efs t1 t1' ?? Hprim]; simplify_eq.
    destruct t1 as [|? [|]]; simplify_eq/=.
    have [Hefs [Hinstrs [Hcharged [Hnb Hcase]]]] := seq_step_progress _ _ _ _ _ _ Hprim Hch.
    subst efs.
    have [Hle [Hdone Hcont]] := IH e2 σ2' eq_refl eq_refl ltac:(by rewrite Hcharged Hinstrs).
    rewrite Hinstrs in Hcont. rewrite Hnb.
    destruct Hcase as [[Hnb' Hf]|[[Hnb' [Hlen Hf]]|[Hnb' [Hlen Hf]]]];
      rewrite Hf in Hle Hcont; split_and!; intros;
      first [done | lia | rewrite (Hdone Hnb'); nia | specialize (Hcont Hnb'); lia].
Qed.

Lemma fetches_bound_steps `{!Arch} (instrs : gmap addr isla_trace) (mem : mem_map) (regs : reg_map) n κs t2 σ2 :
  nsteps n ([initial_local_state regs], {| seq_instrs := instrs; seq_mem := mem; seq_charged := dom instrs; seq_fetches := 0 |}) κs (t2, σ2) →
  n ≤ S σ2.(seq_fetches) * S (max_trace_length instrs).
Proof.
  move => /fetches_bound_steps_aux [//|_ [_ Hbound]].
  specialize (Hbound eq_refl). simpl in Hbound. lia.
Qed.
