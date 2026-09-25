(* UpAblEps49Body.v —— 定理 4.9 本体（RLHF 最优性 eps 化）的下游配套件：          *) (* list 载体无附加接口假设版。                                              *)
(* 使命：S08_RealMainlineDPO.v 节 RealRLHFMain 主定理 real_rlhf_optimal_eps *) (*   （RLHF 最优性 eps 化）在本件载体上重演为无附加接口假设版：其证明体                      *)
(*   使用的两个接口假设——real_kl_decomp_full（自由能常数消去）与                    *) (*   real_gibbs_sum_eps（Σ 版 KL ≥ 0 + eps）——全部替换为已证实例             *)
(*   （e49l 主件 + e49f 件 5），产出 4.9 本体的下游配套件。                       *) (* 替换点定位：                                                        *)
(*   其一（S08 的 assert Hkl，by exact (real_kl_decomp_full pi Hpi Hnormpi)） *) (*     → 改用 e49l_real_kl_decomp_full_list X l e D D_pos pi Hpi Hnormpi *)
(*     （list 载体假设形完全实例）。                                         *) (*   其二（S08 的 assert Hg，by exact (real_gibbs_sum_eps pi Hpi Hnormpi *)
(*     eps Hepspos)）→ 改用 e49f_gibbs_sum_eps X l e D D_pos Z Zpos HZ *) (*     pi Hpi Hnormpi eps Hepspos（直连 S08 已证 real_gibbs_inequality_eps； *)
(*     其内部使用 e49f_boltzmann_normalized）。                         *) (* 装配路线（证明项一致性）：                                                 *)
(*   载体选取沿 e49l：S := X（任意 Set 载体）、sumf := e49l_sumf X l          *) (*   （real_list_sum 折叠）、e := base_loss、Z 取配分定义形                  *)
(*   e49b_part_Z := Σ exp(−e/D)（real_list_sum 形）。                *) (*   关键点＝Z 正性的证明项：real_inv_pos（S03）对见证 eps0 计算相关                 *)
(*   （destruct Hx 拆分 sigT 并把 eps0 编入柯西证人对），故 e49l 主件             *) (*   结论面的 B 词项携带「逐 p 内导的证明项」W(p) :=                              *)
(*   e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp)…； *) (*   直接把 e49l 主件部分应用代入出节 4.9 的固定证明项位置，会因 W(p)                    *)
(*   与固定 W 不可互换而类型不匹配。本件解法＝证明项一致内联形：                             *)
(*   主件语句把证明项沿 e49l 同款逐 p 内联（e49b_part_pos /                     *)
(*   e49b_boltz(_pos) 以 p、Hnormp 为参），使替换件结论面与主件语句面               *)
(*   逐字同源——非空性由 Hnormpi 内导，语句前提面＝4.9 原形                          *)
(*   （pi/Hpi/Hnormpi/eps），不增减弱化前提。                               *)
(*   证明体四段（Hkl、Hd、Hf、opp 环恒等链）沿 S08 原证明逐字重演，                     *)
(*   仅按载体替换表换词：real_sum_over_S ↦ e49l_sumf X l、                  *)
(*   real_base_loss ↦ e、real_boltzmann_dist_r(_pos) ↦ e49b_boltz(_pos) *)
(*   X l e D D_pos pi Hnormpi、real_free_energy ↦ 出节形补 X sumf e D。 *)
(* 使用清单：UpAblEps49List（e49l 主件、三结构前提、非空导出、配分正性）；                 *)
(*   UpAblEps49Fam（e49f 件 5 gibbs 假设实例，经 coqchk 核验公理清点为空         *)
(*   后使用）；CW_ConstructiveWorld_219（S01-S15 出节形适配层）。              *)
(* 构造性注记：零承认；纯构造性；Set 层承载（语句面全 forall 型，                         *)
(*   real_eq/real_lt 全 Set 值）；提取零魔术常量（独立目录）。                     *)
(* 依赖：CW_ConstructiveWorld_219、UpAblEps49List、UpAblEps49Fam、     *)
(*   Stdlib Lists.List。                                          *)
(* 对标：mathlib RLHF 目标的最优性上界（KL 惩罚形式）有限实例。                        *)
(* 编译配方：Rocq 9.1 直调 + cpu_guard；编译输出 -o 临时目录，树内不动。               *)

Require Import CW_ConstructiveWorld_219.
Require Import UpAblEps49List.
Require Import UpAblEps49Fam.
From Stdlib Require Import Lists.List.

(* 配分定义形 Z 与其正性证明项（逐 p 内导非空）                                     *)
Definition e49b_part_Z (X : Set) (l : list X) (e : X -> Real) (D : Real)
           (D_pos : real_lt real_zero D) : Real :=
  real_list_sum X (fun s : X => real_exp_neg
                     (real_mult (real_inv_pos D D_pos) (e s))) l.

Definition e49b_part_pos (X : Set) (l : list X) (e : X -> Real) (D : Real)
           (D_pos : real_lt real_zero D)
           (p : X -> Real) (Hnormp : real_eq (real_list_sum X p l) real_one) :
  real_lt real_zero (e49b_part_Z X l e D D_pos) :=
  e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp) e D D_pos.

(* 载体上的 Boltzmann 分布词项（证明项一致内联形）                                 *)
Definition e49b_boltz (X : Set) (l : list X) (e : X -> Real) (D : Real)
           (D_pos : real_lt real_zero D)
           (p : X -> Real) (Hnormp : real_eq (real_list_sum X p l) real_one)
           (s : X) : Real :=
  real_boltzmann_dist_r X e D D_pos
           (e49b_part_Z X l e D D_pos)
           (e49b_part_pos X l e D D_pos p Hnormp) s.

Definition e49b_boltz_pos (X : Set) (l : list X) (e : X -> Real) (D : Real)
           (D_pos : real_lt real_zero D)
           (p : X -> Real) (Hnormp : real_eq (real_list_sum X p l) real_one)
           (s : X) : real_lt real_zero (e49b_boltz X l e D D_pos p Hnormp s) :=
  real_boltzmann_dist_r_pos X e D D_pos
           (e49b_part_Z X l e D D_pos)
           (e49b_part_pos X l e D D_pos p Hnormp) s.

(* 主件：4.9 本体 list 载体无附加接口假设版                                     *)
(* 语句面与 S08 的 real_rlhf_optimal_eps 逐字同构（载体替换表内联）；前提面＝原形：        *)
(* X l e D D_pos pi Hpi Hnormpi eps，非空性由 Hnormpi 内导、配分 Z 取       *)
(* 定义形、正性证明项逐 p 内联（e49b_part_pos）。两处假设位全部替换为已证实例。                *)
Theorem e49b_real_rlhf_optimal_eps_list :
  forall (X : Set) (l : list X) (e : X -> Real) (D : Real)
         (D_pos : real_lt real_zero D)
    (pi : X -> Real) (Hpi : forall s : X, real_lt real_zero (pi s))
    (Hnormpi : real_eq (e49l_sumf X l pi) real_one) (eps : Real),
    real_lt real_zero eps ->
    real_le (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
            (real_plus
               (real_opp (real_free_energy X (e49l_sumf X l) e D
                            (e49b_boltz X l e D D_pos pi Hnormpi)
                            (e49b_boltz_pos X l e D D_pos pi Hnormpi)))
               (real_mult D eps)).
Proof.
  intros X l e D D_pos pi Hpi Hnormpi eps Hepspos.
  set (B := e49b_boltz X l e D D_pos pi Hnormpi).
  set (Bpos := e49b_boltz_pos X l e D D_pos pi Hnormpi).
  set (klsum := (e49l_sumf X l)
                  (fun s : X => real_kl_term (pi s) (B s) (Hpi s) (Bpos s))).
  (* 1. 替换 S08 使用处一：real_kl_decomp_full 假设 → e49l 主件               *)
  (* （F(π) == F(p_b) + D·Σkl，假设形完全实例）。                             *)
  assert (Hkl : real_eq (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                        (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                   (real_mult D klsum)))
    by exact (e49l_real_kl_decomp_full_list X l e D D_pos pi Hpi Hnormpi).
  (* 2. 替换 S08 使用处二：real_gibbs_sum_eps 假设 → e49f 件 5               *)
  (*    （0 ≤ Σkl + eps；HZ 自反：Z 取配分定义形）。                    *)
  assert (Hg : real_le real_zero (real_plus klsum eps))
    by exact (e49f_gibbs_sum_eps X l e D D_pos
               (e49b_part_Z X l e D D_pos)
               (e49b_part_pos X l e D D_pos pi Hnormpi)
               (real_eq_refl (e49b_part_Z X l e D D_pos))
               pi Hpi Hnormpi eps Hepspos).
  (* 3. 0 ≤ D·Σkl + D·eps（D 正乘 + real_distrib）——S08 同款             *)
  assert (Hd : real_le real_zero (real_plus (real_mult D klsum)
                                             (real_mult D eps))).
  {
    apply (real_le_trans real_zero
                         (real_mult D (real_plus klsum eps))
                         (real_plus (real_mult D klsum) (real_mult D eps))).
    - apply (real_le_trans _ (real_mult D real_zero) _).
      + apply (RealSetoid.real_eq_le real_zero (real_mult D real_zero)).
        apply (real_eq_sym _ _ (real_mult_zero D)).
      + apply (RealSetoid.real_le_id_l (real_mult D real_zero) (real_mult real_zero D)
                                       (real_mult D (real_plus klsum eps))).
        * apply (real_mult_comm D real_zero).
        * apply (RealSetoid.real_le_id_r (real_mult real_zero D)
                                         (real_mult (real_plus klsum eps) D)
                                         (real_mult D (real_plus klsum eps))).
          -- apply (real_mult_comm (real_plus klsum eps) D).
          -- apply (real_le_mult_compat real_zero (real_plus klsum eps) D D_pos Hg).
    - apply (RealSetoid.real_eq_le (real_mult D (real_plus klsum eps))
                                   (real_plus (real_mult D klsum) (real_mult D eps))).
      apply (real_distrib D klsum eps).
  }
  (* 4. F(p_b) ≤ F(π) + D·eps（real_le_plus_compat + Hkl 反向）——S08 同款 *)
  assert (Hf : real_le (real_free_energy X (e49l_sumf X l) e D B Bpos)
                       (real_plus (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                                  (real_mult D eps))).
  {
    apply (real_le_trans _ (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                      (real_plus (real_mult D klsum)
                                                 (real_mult D eps))) _).
    - (* F(p_b) == F(p_b) + 0 ≤ F(p_b) + (D·Σkl + D·eps) *)
      apply (real_le_trans _ (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                        real_zero) _).
      + apply (RealSetoid.real_eq_le (real_free_energy X (e49l_sumf X l) e D B Bpos)
                          (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos) real_zero)).
        apply (real_eq_sym _ _ (real_plus_zero (real_free_energy X (e49l_sumf X l) e D B Bpos))).
      + apply (real_le_plus_compat (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                   (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                   real_zero
                                   (real_plus (real_mult D klsum) (real_mult D eps))
                                   (real_le_refl (real_free_energy X (e49l_sumf X l) e D B Bpos))
                                   Hd).
    - (* F(p_b) + (D·Σkl + D·eps) == F(π) + D·eps（结合 + Hkl 反向） *)
      apply (RealSetoid.real_eq_le (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                   (real_plus (real_mult D klsum) (real_mult D eps)))
                        (real_plus (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                                   (real_mult D eps))).
      apply (real_eq_trans _ (real_plus (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                                   (real_mult D klsum))
                                        (real_mult D eps)) _).
      + apply (real_plus_assoc (real_free_energy X (e49l_sumf X l) e D B Bpos)
                               (real_mult D klsum)
                               (real_mult D eps)).
      + apply (RealSetoid.real_eq_plus_compat (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                                         (real_mult D klsum))
                                              (real_mult D eps)
                                              (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                                              (real_mult D eps)
                                              (real_eq_sym _ _ Hkl) (real_eq_refl _)).
  }
  (* 5. 取负：J(π) ≤ J(p_b) + D·eps——S08 同款环恒等链                       *)
  assert (Hopp' : real_le (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                     (real_opp (real_mult D eps)))
                          (real_opp (real_free_energy X (e49l_sumf X l) e D B Bpos))).
  {
    apply (RealSetoid.real_le_id_l (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                              (real_opp (real_mult D eps)))
                                   (real_opp (real_plus (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                                                        (real_mult D eps)))
                                   (real_opp (real_free_energy X (e49l_sumf X l) e D B Bpos))).
    - apply (real_eq_sym _ _ (real_opp_plus (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                                            (real_mult D eps))).
    - apply (real_opp_le_compat (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                (real_plus (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                                           (real_mult D eps))
                                Hf).
  }
  apply (real_le_trans (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                       (real_plus (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                             (real_opp (real_mult D eps)))
                                  (real_mult D eps))
                       (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D B Bpos))
                                  (real_mult D eps))).
  - (* A == (A + opp C) + C：环恒等（real_plus_assoc 反向 + real_plus_comm 内层 + real_plus_opp + real_plus_zero） *)
    assert (Hring : real_eq (real_plus (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                                  (real_opp (real_mult D eps)))
                                       (real_mult D eps))
                            (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))).
    {
      apply (real_eq_trans _ (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                        (real_plus (real_opp (real_mult D eps))
                                                   (real_mult D eps))) _).
      - apply (real_eq_sym _ _ (real_plus_assoc (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                                (real_opp (real_mult D eps))
                                                (real_mult D eps))).
      - apply (real_eq_trans _ (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                          (real_plus (real_mult D eps)
                                                     (real_opp (real_mult D eps)))) _).
        + apply (RealSetoid.real_eq_plus_compat (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                                (real_plus (real_opp (real_mult D eps))
                                                           (real_mult D eps))
                                                (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                                (real_plus (real_mult D eps)
                                                           (real_opp (real_mult D eps)))
                                                (real_eq_refl _)
                                                (real_plus_comm (real_opp (real_mult D eps))
                                                                (real_mult D eps))).
        + apply (real_eq_trans _ (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                            real_zero) _).
          * apply (RealSetoid.real_eq_plus_compat (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                                  (real_plus (real_mult D eps)
                                                             (real_opp (real_mult D eps)))
                                                  (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                                  real_zero
                                                  (real_eq_refl _)
                                                  (real_plus_opp (real_mult D eps))).
          * apply (real_plus_zero (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))).
    }
    apply (RealSetoid.real_eq_le (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                 (real_plus (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                                       (real_opp (real_mult D eps)))
                                            (real_mult D eps))).
    apply (real_eq_sym _ _ Hring).
  - (* (A + opp C) + C ≤ B + C：real_le_plus_compat（Hopp' + real_le_refl） *)
    apply (real_le_plus_compat (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                          (real_opp (real_mult D eps)))
                               (real_opp (real_free_energy X (e49l_sumf X l) e D B Bpos))
                               (real_mult D eps) (real_mult D eps)
                               Hopp' (real_le_refl (real_mult D eps))).
Qed.

(* 依赖审计：零外部未证假设；独立目录提取                                           *)
Print Assumptions e49b_part_Z.
Print Assumptions e49b_part_pos.
Print Assumptions e49b_boltz.
Print Assumptions e49b_boltz_pos.
Print Assumptions e49b_real_rlhf_optimal_eps_list.

From Stdlib Require Import Extraction.
Set Extraction Output Directory "../_x1_body_extract".
(* 单条命令合并提取（多条 Separate Extraction 仅存末条闭包）                       *)
Separate Extraction e49b_part_Z e49b_part_pos e49b_boltz e49b_boltz_pos
  e49b_real_rlhf_optimal_eps_list.
