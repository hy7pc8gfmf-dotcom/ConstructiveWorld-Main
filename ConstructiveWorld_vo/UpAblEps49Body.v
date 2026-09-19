(* ============================================================ *)
(* UpAblEps49Body.v —— X1 席：定理 4.9 本体下游直配件                 *)
(*   （AB3 报告 §六.3 升级方向兑现：沿 S08:2613/:2616 消费位换装），    *)
(*   2026-09-20                                                      *)
(* ============================================================ *)
(* 【使命】把 S08_RealMainlineDPO.v 节 RealRLHFMain 旗舰定理          *)
(*   real_rlhf_optimal_eps（:2601，RLHF 最优性 eps 化）在本体裁体上    *)
(*   重演为「零诚实接口版」：其证明体消费的两个开放接口槽——            *)
(*   :2613 real_kl_decomp_full（自由能常数消去桥）与                  *)
(*   :2616 real_gibbs_sum_eps（Σ 版 KL ≥ 0 + eps）——全部换装为        *)
(*   已放电实例（e49l 主件 + e49f 件5），产出 4.9 本体的下游直配件。    *)
(* ------------------------------------------------------------------ *)
(* 【换装位坐标】                                                     *)
(*   消费位一 S08:2610-2613：assert Hkl … by exact (槽 pi Hpi Hnormpi) *)
(*     → 换装 e49l_real_kl_decomp_full_list X l e D D_pos pi Hpi       *)
(*       Hnormpi（list 载体槽真前件形完全放电，AB7 席主件）。           *)
(*   消费位二 S08:2615-2616：assert Hg … by exact (槽 pi Hpi Hnormpi   *)
(*     eps Hepspos) → 换装 e49f_gibbs_sum_eps X l e D D_pos Z Zpos HZ  *)
(*     pi Hpi Hnormpi eps Hepspos（S08 已证 real_gibbs_inequality_eps  *)
(*     直连引擎，AB4 席件5；其内部消费 e49f_boltzmann_normalized）。    *)
(* ------------------------------------------------------------------ *)
(* 【装配路线与见证书（witness 一致性）】                              *)
(*   载体选型照 e49l：S := X（任意 Set 载体）、sumf := e49l_sumf X l    *)
(*   （real_list_sum 折叠）、e := base_loss、Z 取配分定义形             *)
(*   e49b_part_Z := Σ exp(−e/D)（real_list_sum 形）。                  *)
(*   关键装配点＝Z 正性见证书：real_inv_pos（S03:6661）对见证 eps0      *)
(*   计算相关（destruct Hx 拆 sigT 并把 eps0 编入柯西证人对），故       *)
(*   e49l 主件结论面的 B 词项携「逐 p 内导见证」W(p) :=                *)
(*   e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp)…；    *)
(*   直接把 e49l 主件部分应用喂给出节 4.9 的固定见证槽位会因 W(p) 与    *)
(*   固定 W 不可互换而型配失败。本件解法＝见证一致内联形：主件语句把    *)
(*   见证项沿 e49l 同款逐 p 内联（e49b_part_pos / e49b_boltz(_pos)      *)
(*   以 p/Hnormp 为参），使换装件结论面与主件语句面逐字同源——           *)
(*   非空性由 Hnormpi 内导（AB2 第 9 坑范式 / AB7 零增薄同判），         *)
(*   语句前件面＝4.9 原形（pi/Hpi/Hnormpi/eps）零增薄。                *)
(*   证明体四段（Hkl/Hd/Hf/opp 环恒等链）沿 S08:2607-2729 逐字重演，    *)
(*   仅按载体替换表换词：real_sum_over_S ↦ e49l_sumf X l、              *)
(*   real_base_loss ↦ e、real_boltzmann_dist_r(_pos) ↦ e49b_boltz(_pos) *)
(*   X l e D D_pos pi Hnormpi、real_free_energy ↦ 出节形补 X sumf e D。 *)
(* ------------------------------------------------------------------ *)
(* 【直接材料（消费勿重造）】                                         *)
(*   UpAblEps49List（e49l 主件/三结构/非空导出/配分正性，AB7）；        *)
(*   UpAblEps49Fam（e49f 件5 gibbs 槽实例，AB4，盘面 coqchk RC=0        *)
(*   公理清点为空实测核验后消费）；CW_ConstructiveWorld_219（S01-S15    *)
(*   出节形垫片）。                                                    *)
(* 【红线自检】零承认件；纯构造性（零未闭合证明、零经典逻辑）；        *)
(*   Set 层零泄露（语句面全 forall 型，real_eq/real_lt 全 Set 值）；    *)
(*   提取零魔术常量（独立目录一人一目录）；未触碰任何既有文件；         *)
(*   禁入 order.txt/_CoqProject（注册归主会话）。                      *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpAblEps49List.
Require Import UpAblEps49Fam.
From Stdlib Require Import Lists.List.

(* ===== 1. 配分定义形 Z 与其正性见证（逐 p 内导非空，AB7 同款） ===== *)
Definition e49b_part_Z (X : Set) (l : list X) (e : X -> Real) (D : Real)
           (D_pos : real_lt real_zero D) : Real :=
  real_list_sum X (fun s : X => real_exp_neg
                     (real_mult (real_inv_pos D D_pos) (e s))) l.

Definition e49b_part_pos (X : Set) (l : list X) (e : X -> Real) (D : Real)
           (D_pos : real_lt real_zero D)
           (p : X -> Real) (Hnormp : real_eq (real_list_sum X p l) real_one) :
  real_lt real_zero (e49b_part_Z X l e D D_pos) :=
  e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp) e D D_pos.

(* ===== 2. 载体上的 Boltzmann 分布词项（见证一致内联形） ===== *)
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

(* ===== 3. 主件：4.9 本体 list 载体零诚实接口版 ===== *)
(* 语句面与 S08:2601-2606 逐字同构（载体替换表内联）；前件面＝原形零增薄： *)
(* X l e D D_pos pi Hpi Hnormpi eps，非空性由 Hnormpi 内导、配分 Z 取    *)
(* 定义形、正性见证逐 p 内联（e49b_part_pos）。两槽位全部换装为放电实例。  *)
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
  (* 1. 消费位 S08:2613 换装：real_kl_decomp_full 槽 → e49l 主件       *)
  (*    （F(π) == F(p_b) + D·Σkl，槽真前件形完全放电）。                *)
  assert (Hkl : real_eq (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                        (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                   (real_mult D klsum)))
    by exact (e49l_real_kl_decomp_full_list X l e D D_pos pi Hpi Hnormpi).
  (* 2. 消费位 S08:2616 换装：real_gibbs_sum_eps 槽 → e49f 件5          *)
  (*    （0 ≤ Σkl + eps；HZ 自反：Z 取配分定义形）。                    *)
  assert (Hg : real_le real_zero (real_plus klsum eps))
    by exact (e49f_gibbs_sum_eps X l e D D_pos
               (e49b_part_Z X l e D D_pos)
               (e49b_part_pos X l e D D_pos pi Hnormpi)
               (real_eq_refl (e49b_part_Z X l e D D_pos))
               pi Hpi Hnormpi eps Hepspos).
  (* 3. 0 ≤ D·Σkl + D·eps（D 正乘 + distrib）——S08:2617-2639 同款 *)
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
  (* 4. F(p_b) ≤ F(π) + D·eps（le_plus_compat + Hkl 换形）——S08:2641-2676 同款 *)
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
  (* 5. opp 取负：J(π) ≤ J(p_b) + D·eps——S08:2682-2728 同款环恒等链 *)
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
  - (* A == (A + opp C) + C：环恒等（assoc 反向 + comm 内层 + plus_opp + plus_zero） *)
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
  - (* (A + opp C) + C ≤ B + C：le_plus_compat（Hopp' + refl C） *)
    apply (real_le_plus_compat (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                          (real_opp (real_mult D eps)))
                               (real_opp (real_free_energy X (e49l_sumf X l) e D B Bpos))
                               (real_mult D eps) (real_mult D eps)
                               Hopp' (real_le_refl (real_mult D eps))).
Qed.

(* ===== 证据区：零外部未证假设 + 独立目录提取（一人一目录） ===== *)
Print Assumptions e49b_part_Z.
Print Assumptions e49b_part_pos.
Print Assumptions e49b_boltz.
Print Assumptions e49b_boltz_pos.
Print Assumptions e49b_real_rlhf_optimal_eps_list.

From Stdlib Require Import Extraction.
Set Extraction Output Directory "../_x1_body_extract".
(* 单条命令合并提取（多条 Separate Extraction 仅存末条闭包——AB7 坑规避） *)
Separate Extraction e49b_part_Z e49b_part_pos e49b_boltz e49b_boltz_pos
  e49b_real_rlhf_optimal_eps_list.
