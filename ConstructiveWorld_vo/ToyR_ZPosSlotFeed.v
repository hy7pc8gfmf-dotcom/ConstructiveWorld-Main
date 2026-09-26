(* ==========================================================================)
   ToyR_ZPosSlotFeed.v — 配分与分区的正性供给面
   使命: zsf_sigmig2_Z_align_a_pos、zsf_iter_Z_thermo_i_pos、zsf_gibbs_Z_thermo_r_pos（配分正性）与 zsf_gibbs_evicted_partition_r_pos/zsf_restb_req_evicted_partition_pos_of_carrier（逐出分区正性）。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSumD、UpReqBranchPos、G12_ZPosFam
   对标: Gibbs 配分函数与逐出分区和的正性（正测度性）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqBranchPos.
Require Import G12_ZPosFam.
Import RealInterfaceEnhancedMod.

(* ---- 槽⑤ UpSigMigrate2.v:891 Z_align_a_pos 纯实例化 ---- *)
Theorem zsf_sigmig2_Z_align_a_pos :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set) (enum : list S)
         (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
         (Hne : Not (enum = nil)),
    lt zero (@UpSigMigrate2.Z_align_a_sum R RIS S (@sumd_sumf R RIS S enum)
               reward beta beta_pos pi_ref).
Proof.
  exact zpi2_sigmig2_Z_align_a_pos.
Qed.

(* ---- 槽⑥ UpReqAttnIter.v:130 Z_thermo_i_pos 纯实例化 ---- *)
Theorem zsf_iter_Z_thermo_i_pos :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set) (enum : list S)
         (D : R) (D_pos : lt zero D) (energy : S -> R)
         (Hne : Not (enum = nil)),
    lt zero (@UpReqAttnIter.Z_thermo_i R RIS S (@sumd_sumf R RIS S enum)
               D D_pos energy).
Proof.
  exact zpi2_iter_Z_thermo_i_pos.
Qed.

(* ---- 槽⑦ UpReqAttnGibbs.v:547 Z_thermo_r_pos 纯实例化 ---- *)
Theorem zsf_gibbs_Z_thermo_r_pos :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set) (enum : list S)
         (D : R) (D_pos : lt zero D) (energy : S -> R)
         (Hne : Not (enum = nil)),
    lt zero (@UpReqAttnGibbs.Z_thermo_r R RIS S (@sumd_sumf R RIS S enum)
               D D_pos energy).
Proof.
  exact zpi2_gibbs_Z_thermo_r_pos.
Qed.

(* ---- 槽⑳ UpReqAttnGibbs.v:701 evicted_partition_r_pos 条件形并入 ----
   结论载体 = brp_evicted_partition_r，即宿主 evicted_partition_r 的
   sumd 键填充实例（brp_boltzmann_factor_r ≡ 宿主 boltzmann_factor_r）。 *)
Theorem zsf_gibbs_evicted_partition_r_pos :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set) (enum : list S)
         (D : R) (D_pos : lt zero D) (energy : S -> R)
         (keep : S -> Set) (keep_dec : forall s : S, Or (keep s) (Not (keep s)))
         (Hw : sigT (fun s : S => prod (InT s enum)
                (match keep_dec s with
                 | inl _ => unit
                 | inr _ => Empty_set
                 end))),
    lt zero (@UpReqBranchPos.brp_evicted_partition_r
               R RIS S enum D D_pos energy keep keep_dec).
Proof.
  intros R RIS S enum D D_pos energy keep keep_dec Hw.
  exact (@brp_b3_evicted_partition_r_pos           R RIS S enum D D_pos energy keep keep_dec Hw).
Qed.

(* ---- 槽㉑ UpReqAlignRestB.v:1767 req_evicted_partition_pos 条件形并入 ----
   裸载体回接形：结论取宿主同款 match 分支和（brp_kv_boltzmann_factor
   ≡ 宿主 req_kv_boltzmann_factor，逐字同构），载体 sov 携规范条件位。 *)
Theorem zsf_restb_req_evicted_partition_pos_of_carrier :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set) (enum : list S)
         (D : R) (D_pos : lt zero D) (energy : S -> R)
         (keep : S -> Set) (keep_dec : forall s : S, Or (keep s) (Not (keep s)))
         (sov : (S -> R) -> R),
    (forall g : S -> R, req (sov g) (@sumd_sumf R RIS S enum g)) ->
    sigT (fun s : S => prod (InT s enum)
            (match keep_dec s with
             | inl _ => unit
             | inr _ => Empty_set
             end)) ->
    lt zero (sov (fun s : S =>
            match keep_dec s with
            | inl _ => @UpReqBranchPos.brp_kv_boltzmann_factor
                         R RIS S D D_pos energy s
            | inr _ => zero
            end)).
Proof.
  intros R RIS S enum D D_pos energy keep keep_dec sov Hspec Hw.
  exact (@brp_b4_of_carrier R RIS S enum D D_pos energy keep keep_dec           sov Hspec Hw).
Qed.

(* ============ 自检段（G4 口径：逐件 Closed 实证） ===================== *)

Print Assumptions zsf_sigmig2_Z_align_a_pos.
Print Assumptions zsf_iter_Z_thermo_i_pos.
Print Assumptions zsf_gibbs_Z_thermo_r_pos.
Print Assumptions zsf_gibbs_evicted_partition_r_pos.
Print Assumptions zsf_restb_req_evicted_partition_pos_of_carrier.
