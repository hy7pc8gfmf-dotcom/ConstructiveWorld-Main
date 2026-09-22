(* ============================================================ *)
(* ToyR 玩具证替换件 —— T269 台账席 战役包AD（tier2 末批二）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   rfep_kl_term_equiv_real（原 L164，3 句玩具证）                       *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T339 恒等守恒更正注记】2026-09-22 包AW十四 台账席（恒等头注更正第四批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查定谳、T317（包AV六）试点定谳：本件实测为 *)
(* 恒等守恒——清单所列 1 槽证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 槽＋恒等守恒 1 槽；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337／T339 台账。 *)
(* 附记：T277 判级全文恒等；Y 域收尾＋AB 域收尾＋AD 域直推第四批（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqRealFEP.v *)
(* *)
(* 目的： 自由能原理的 Real 层等式基座（R2-2 补强）。 *)
(* 主件： rfep_real_kl_decomp_full KL 完整分解与 rfep_boltzmann_normalized_real 归一化族。 *)
(* 依赖： CW_ConstructiveWorld_219、G05_LogSmall。 *)
(* 备注： 主件唯一残留环境前提为 Hnormb（质量和等于一），逐 eps 档 Variable 位逐位申报（诚实前提申报）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqRealFEP.v —— 第二轮非平凡补强 R2-2（任务书②等式基座席）：        *)
(*   real_free_energy_kl_decomp 等式基座——四条装配链枢纽                *)
(*   2026-09-10                                                         *)
(* ------------------------------------------------------------------ *)
(* 【使命】论文2 定理 4.1 `free_energy_kl_decomp` 的 Real 层等式镜像：    *)
(*   F[p] ≡ F[p_b] + D·KL(p‖p_b)。符号与函数形态以 L20290         *)
(*   `rlhf_free_energy_kl`（Id 锚：F[π] ≡ F[π*] + β·relative_entropy）   *)
(*   与论文 §4 口径为准；Real 层 KL 承载 = real_kl_term 逐项和（*)
(*   L41696 规范形），D 因子逐字保留（L43730 槽形 real_mult D）。  *)
(* ------------------------------------------------------------------ *)

(*   ① UpReqLogCompD.logc_real_kl_decomp_full（L878，Real 层             *)
(*      real_kl_term 形）为 real_list_sum 具体 list 载体（显式 l），     *)
(*      不可直接喂抽象 sumf 载体的 假设位——载体不同轴，两步换形不可达；*)
(*   ② UpSigMigrate2.req_free_energy_kl_decomp（L666）/ sig2_tail_      *)
(*      stage1.a_fe_kl_decomp（req 层草案，无 .vo）为 req 载体 rminus    *)
(*      字面形（非 real_kl_term 具名形）——层位与形态双不同；            *)
(*   ③ Section RealRLHFMain 的 real_kl_decomp_full（L43730）与    *)
(*      UpRealLeB Section RealRLHFLeB 的同名槽（L218，被                 *)
(*      real_rlhf_optimal_B L235 直接消费）均为 **Variable 未证明假设位**。 *)
(*   ⇒ 本件真缺口：抽象 sumf 载体（ext/add/linear 接口）+ RLHF     *)
(*   具名接口（real_boltzmann_dist_r / real_free_energy / real_kl_term   *)
(*   全具名同符号）上的 **证明件**，即上述两 Variable 槽的消解件。       *)
(*   伴件 rfep_rlhf_free_energy_kl（base=π* 锚签名替换）为纯装配，       *)

(* ------------------------------------------------------------------ *)
(* 【诚实前提申报】主件唯一残留环境前提 = Hnormb（Σ p_b == 1）；          *)
(*   附件 rfep_boltzmann_normalized_real 以单条 partition 条件（Σ exp    *)
(*   == Z）显式前提供给之；log 分解件 rfep_boltzmann_log_decomp_real     *)
(*   为零前提直证（Hpart-free，实读 real_log_mult/real_log_one/    *)
(*   real_log_exp_neg 根基元全链闭合）。载体代数 ext/add/linear 为节     *)

(*   原节无此字段，系因该槽原为 Variable 不需证明；消解所需最小增量）。  *)
(* ------------------------------------------------------------------ *)
(* 【⑤⑥消费接口说明】                                                  *)
(*   ⑤ R2-5 间隙恒等 4.3/4.4 镜像（real_rlhf_suboptimality_gap：        *)
(*      J*−J(π) ≡ β·KL）：消费 rfep_rlhf_free_energy_kl——J := −F，      *)
(*      移项即得 F(π)−F(π＊) ≡ D·Σ kl_term(π,π＊)；KL≥0 半边沿              *)
(*      real_gibbs_inequality_eps（L41704）/ logd_gibbs_sum_eps_  *)
(*      boltzmann_list（G05_LogSmall Part E）承重，不属本件。              *)
(*   ⑥ R2-6 唯一性 4.2 镜像（real_rlhf_optimal_unique 前提承载形）：     *)
(*      消费 rfep_rlhf_free_energy_kl 把「目标值相同」化到               *)
(*      D·Σ kl_term ≡ 0，再逐项非负+和零提取逐点相等（C5 边界：等号     *)
(*      消去无条件形不可证，结果语句必须带显式前提）。                  *)
(*   假设位显式应用：实例化 real_rlhf_optimal_eps / UpRealLeB            *)
(*      real_rlhf_optimal_B 时，real_kl_decomp_full 参数位以             *)
(*      rfep_real_kl_decomp_full S sumf ext add linear e D Dp Z Zp       *)
(*      Hnormb（部分应用）喂入；real_kl_term_equiv 槽以件1 喂入；        *)
(*      real_boltzmann_normalized 槽以件5b + partition 实例喂入；        *)
(*      real_boltzmann_log_decomp 槽以件5a 喂入（零前提）。             *)
(* ------------------------------------------------------------------ *)
(* 【红线】Set 层零 Prop（real_eq/real_lt 全 Set 值）；全 Qed 闭合；     *)
(*   零 公理/承认件/经典逻辑族；既有文件零触碰（/UpReqLogCompD/  *)
(*   UpRealLeB/G05_LogSmall 全只读，只消费 .vo）；real_eq 非 Id 禁 rewrite， *)
(*   全链 real_eq_trans/RealSetoid compat（E393 纪律）；纯等式零 eps     *)
(*   账目（任务书 R2-2 坑位②）。坑卡对表：E404 五桥机组装配方（本件即   *)

(*   只吃第二参 plus 形；E403③ 节泛化跨节消费全参显式。                 *)
(* 编译配方：_rfep_g2.cmd + cpu_guard（CoreN 0-3，LoadLimit 60）         *)


(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import G05_LogSmall.

(* ============================================================ *)
(* Section RFEPMain：抽象 sumf 载体（RealRLHFMain 同名同型接口     *)

(* ============================================================ *)

Section RFEPMain.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).

(* real_list_sum_linear（在案），具体实例可显式应用                   *)
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).
Variable real_base_loss : S -> Real.
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable Z_align_r : Real.
Variable Z_align_r_pos : real_lt real_zero Z_align_r.

(* ---------------------------------------------------------- *)
(* Part 0：载体代数公共机（E404 五桥机之 opp 桥）                        *)
(* ---------------------------------------------------------- *)

(* P0 前置基元：mult_opp_r 型（上游仅 mult_opp_l：a·(−b)≡−(a·b)，经 comm 两步桥出 (−1)·x≡−x） *)
Lemma rfep_mult_opp_r_alt : forall x : Real,
  real_eq (real_mult (real_opp real_one) x) (real_opp x).
Proof.
  intro x.
  apply (real_eq_trans
          (real_mult (real_opp real_one) x)
          (real_mult x (real_opp real_one))
          (real_opp x)).
  - exact (real_mult_comm (real_opp real_one) x).
  - apply (real_eq_trans
            (real_mult x (real_opp real_one))
            (real_opp (real_mult x real_one))
            (real_opp x)).
    + exact (real_mult_opp_l x real_one).
    + apply (RealSetoid.real_eq_opp_compat (real_mult x real_one) x).
      exact (real_mult_one x).
Qed.

(* 左单位基元：上游 real_mult_one 仅右单位形（x·1≡x），comm 一步桥出 1·x≡x *)
Lemma rfep_mult_one_l : forall x : Real,
  real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans
          (real_mult real_one x)
          (real_mult x real_one)
          x).
  - exact (real_mult_comm real_one x).
  - exact (real_mult_one x).
Qed.

(* P0：Σ (−f) == −(Σ f)（linear + mult_opp_l 两步组装） *)
Lemma rfep_sum_opp : forall (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_opp (f s)))
          (real_opp (real_sum_over_S f)).
Proof.
  intro f.
  apply (real_eq_trans
           (real_sum_over_S (fun s : S => real_opp (f s)))
           (real_mult (real_opp real_one) (real_sum_over_S f))
           (real_opp (real_sum_over_S f))).
  - apply (real_eq_trans
             (real_sum_over_S (fun s : S => real_opp (f s)))
             (real_sum_over_S (fun s : S => real_mult (real_opp real_one) (f s)))
             (real_mult (real_opp real_one) (real_sum_over_S f))).
    + apply real_eq_sym. apply real_sum_over_S_ext.
      intro s.
      exact (rfep_mult_opp_r_alt (f s)).
    + exact (real_sum_over_S_linear (real_opp real_one) f).
  - exact (rfep_mult_opp_r_alt (real_sum_over_S f)).
Qed.

(* ---------------------------------------------------------- *)
(* Part 1：件1——real_kl_term_equiv 槽的 Real 实例（字面形 → kl_term）    *)
(*   （G05_LogSmall logd_kl_term_minus_form 的互逆双形，假设位同形喂件）      *)
(* ---------------------------------------------------------- *)

Lemma rfep_kl_term_equiv_real :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)) (s : S),
  real_eq
    (real_mult (p s)
       (real_plus (real_log (p s) (Hp s))
                  (real_opp
                     (real_log
                        (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                        (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))))
    (real_kl_sum_term S real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp s).
Proof.
  intros p Hp s.
  apply real_eq_sym.
  exact (logd_kl_term_minus_form (p s)           (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)           (Hp s)           (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)).
Qed.

(* ---------------------------------------------------------- *)
(* Part 2：件5a——real_boltzmann_log_decomp 槽的 Real 填件（零前提）      *)

(*   （real_log_one + inv_pos_correct 组装）+ real_log_exp_neg 显式应用      *)
(* ---------------------------------------------------------- *)

Lemma rfep_boltzmann_log_decomp_real :
  forall (s : S)
    (Hpb : real_lt real_zero
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)),
  real_eq
    (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s) Hpb)
    (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                         (real_log Z_align_r Z_align_r_pos))).
Proof.
  intros s Hpb.
  set (Es := real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s))).
  set (Hi := real_inv_pos_pos Z_align_r Z_align_r_pos).
  set (Hes := real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (real_base_loss s))).
  set (Hcanon := real_mult_positive (real_inv_pos Z_align_r Z_align_r_pos) Es Hi Hes).
  
  assert (Hinv : real_eq (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
                         (real_opp (real_log Z_align_r Z_align_r_pos))).
  { assert (Hsum : real_eq (real_plus (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
                                      (real_log Z_align_r Z_align_r_pos))
                           real_zero).
    { apply (real_eq_trans
               (real_plus (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
                          (real_log Z_align_r Z_align_r_pos))
               (real_log (real_mult (real_inv_pos Z_align_r Z_align_r_pos) Z_align_r)
                         (real_mult_positive (real_inv_pos Z_align_r Z_align_r_pos) Z_align_r
                            Hi Z_align_r_pos))
               real_zero).
      - apply real_eq_sym.
        exact (real_log_mult (real_inv_pos Z_align_r Z_align_r_pos) Z_align_r Hi Z_align_r_pos).
      - apply (real_eq_trans
                 (real_log (real_mult (real_inv_pos Z_align_r Z_align_r_pos) Z_align_r)
                           (real_mult_positive (real_inv_pos Z_align_r Z_align_r_pos) Z_align_r
                              Hi Z_align_r_pos))
                 (real_log real_one real_lt_zero_one)
                 real_zero).
        + apply (real_log_wd
                   (real_mult (real_inv_pos Z_align_r Z_align_r_pos) Z_align_r)
                   real_one
                   (real_mult_positive (real_inv_pos Z_align_r Z_align_r_pos) Z_align_r
                      Hi Z_align_r_pos)
                   real_lt_zero_one).
          apply (real_eq_trans
                   (real_mult (real_inv_pos Z_align_r Z_align_r_pos) Z_align_r)
                   (real_mult Z_align_r (real_inv_pos Z_align_r Z_align_r_pos))
                   real_one).
          * exact (real_mult_comm (real_inv_pos Z_align_r Z_align_r_pos) Z_align_r).
          * exact (real_inv_pos_correct Z_align_r Z_align_r_pos).
        + exact (real_log_one real_lt_zero_one). }
    apply (real_eq_trans
             (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
             (real_plus (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi) real_zero)
             (real_opp (real_log Z_align_r Z_align_r_pos))).
    - apply real_eq_sym.
      exact (real_plus_zero (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)).
    - apply (real_eq_trans
               (real_plus (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi) real_zero)
               (real_plus (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
                          (real_plus (real_log Z_align_r Z_align_r_pos)
                                     (real_opp (real_log Z_align_r Z_align_r_pos))))
               (real_opp (real_log Z_align_r Z_align_r_pos))).
      + apply (RealSetoid.real_eq_plus_compat_adapt
                 (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
                 (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
                 real_zero
                 (real_plus (real_log Z_align_r Z_align_r_pos)
                            (real_opp (real_log Z_align_r Z_align_r_pos)))
                 (real_eq_refl _)).
        apply real_eq_sym.
        exact (real_plus_opp (real_log Z_align_r Z_align_r_pos)).
      + apply (real_eq_trans
                 (real_plus (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
                            (real_plus (real_log Z_align_r Z_align_r_pos)
                                       (real_opp (real_log Z_align_r Z_align_r_pos))))
                 (real_plus (real_plus (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
                                       (real_log Z_align_r Z_align_r_pos))
                            (real_opp (real_log Z_align_r Z_align_r_pos)))
                 (real_opp (real_log Z_align_r Z_align_r_pos))).
        * exact (real_plus_assoc (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
                    (real_log Z_align_r Z_align_r_pos)
                    (real_opp (real_log Z_align_r Z_align_r_pos))).
        * apply (real_eq_trans
                   (real_plus (real_plus (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
                                         (real_log Z_align_r Z_align_r_pos))
                              (real_opp (real_log Z_align_r Z_align_r_pos)))
                   (real_plus real_zero (real_opp (real_log Z_align_r Z_align_r_pos)))
                   (real_opp (real_log Z_align_r Z_align_r_pos))).
          -- apply (RealSetoid.real_eq_plus_compat_adapt
                      (real_plus (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
                                 (real_log Z_align_r Z_align_r_pos))
                      real_zero
                      (real_opp (real_log Z_align_r Z_align_r_pos))
                      (real_opp (real_log Z_align_r Z_align_r_pos))
                      Hsum (real_eq_refl _)).
          -- apply (real_eq_trans
                       (real_plus real_zero (real_opp (real_log Z_align_r Z_align_r_pos)))
                       (real_plus (real_opp (real_log Z_align_r Z_align_r_pos)) real_zero)
                       (real_opp (real_log Z_align_r Z_align_r_pos))).
             ++ exact (real_plus_comm real_zero (real_opp (real_log Z_align_r Z_align_r_pos))).
             ++ exact (real_plus_zero (real_opp (real_log Z_align_r Z_align_r_pos))). }
  (* 主链：换见证 → real_log_mult 分解 → Hinv + exp_neg 显式应用 → 完成 *)
  apply (real_eq_trans
           (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s) Hpb)
           (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s) Hcanon)
           (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                (real_log Z_align_r Z_align_r_pos)))).
  - exact (real_log_wd
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
             Hpb Hcanon
             (real_eq_refl (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s))).
  - apply (real_eq_trans
             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s) Hcanon)
             (real_plus (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
                        (real_log Es Hes))
             (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                  (real_log Z_align_r Z_align_r_pos)))).
    + exact (real_log_mult (real_inv_pos Z_align_r Z_align_r_pos) Es Hi Hes).
    + apply (real_eq_trans
               (real_plus (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
                          (real_log Es Hes))
               (real_plus (real_opp (real_log Z_align_r Z_align_r_pos))
                          (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
               (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                    (real_log Z_align_r Z_align_r_pos)))).
      * apply (RealSetoid.real_eq_plus_compat_adapt
                 (real_log (real_inv_pos Z_align_r Z_align_r_pos) Hi)
                 (real_opp (real_log Z_align_r Z_align_r_pos))
                 (real_log Es Hes)
                 (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                 Hinv
                 (real_log_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))).
      * apply (real_eq_trans
                 (real_plus (real_opp (real_log Z_align_r Z_align_r_pos))
                            (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
                 (real_plus (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                            (real_opp (real_log Z_align_r Z_align_r_pos)))
                 (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                      (real_log Z_align_r Z_align_r_pos)))).
        -- exact (real_plus_comm (real_opp (real_log Z_align_r Z_align_r_pos))
                    (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s)))).
        -- apply real_eq_sym.
           exact (real_opp_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                (real_log Z_align_r Z_align_r_pos)).
Qed.

(* ---------------------------------------------------------- *)
(* Part 3：件5b——real_boltzmann_normalized 槽的 Real 填件                *)
(*   （partition 条件 Σ exp(−e/D) == Z 为显式前提，两步归一化：          *)
(*    linear + inv_pos_correct——E404 配方归一化固定两步走）              *)
(* ---------------------------------------------------------- *)

Lemma rfep_boltzmann_normalized_real :
  forall (Hpart : real_eq
                    (real_sum_over_S
                       (fun s : S => real_exp_neg
                                       (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
                    Z_align_r),
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one.
Proof.
  intro Hpart.
  apply (real_eq_trans
           (real_sum_over_S
              (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
           (real_mult (real_inv_pos Z_align_r Z_align_r_pos) Z_align_r)
           real_one).
  - apply (real_eq_trans
             (real_sum_over_S
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
             (real_sum_over_S
                (fun s : S => real_mult (real_inv_pos Z_align_r Z_align_r_pos)
                           (real_exp_neg
                              (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))
             (real_mult (real_inv_pos Z_align_r Z_align_r_pos) Z_align_r)).
    + apply real_sum_over_S_ext. intro s. apply real_eq_refl.
    + apply (real_eq_trans
               (real_sum_over_S
                  (fun s : S => real_mult (real_inv_pos Z_align_r Z_align_r_pos)
                     (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))
               (real_mult (real_inv_pos Z_align_r Z_align_r_pos)
                  (real_sum_over_S
                     (fun s : S => real_exp_neg
                                     (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))
               (real_mult (real_inv_pos Z_align_r Z_align_r_pos) Z_align_r)).
      * exact (real_sum_over_S_linear (real_inv_pos Z_align_r Z_align_r_pos)
                  (fun s : S => real_exp_neg
                                  (real_mult (real_inv_pos D D_pos) (real_base_loss s)))).
      * apply (RealSetoid.real_eq_mult_compat_adapt
                 (real_inv_pos Z_align_r Z_align_r_pos)
                 (real_inv_pos Z_align_r Z_align_r_pos)
                 (real_sum_over_S
                    (fun s : S => real_exp_neg
                                    (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
                 Z_align_r
                 (real_eq_refl _) Hpart).
  - apply (real_eq_trans
             (real_mult (real_inv_pos Z_align_r Z_align_r_pos) Z_align_r)
             (real_mult Z_align_r (real_inv_pos Z_align_r Z_align_r_pos))
             real_one).
    + exact (real_mult_comm (real_inv_pos Z_align_r Z_align_r_pos) Z_align_r).
    + exact (real_inv_pos_correct Z_align_r Z_align_r_pos).
Qed.

(* ---------------------------------------------------------- *)
(* Part 4：能量期望工作马（E404 逐点两叉分解型，抽象载体兑现）           *)

(* ---------------------------------------------------------- *)

Lemma rfep_energy_expect_eq :
  forall (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s))
    (Hnormq : real_eq (real_sum_over_S q) real_one),
  real_eq
    (real_sum_over_S (fun s : S => real_mult (q s) (real_base_loss s)))
    (real_plus
       (real_opp (real_mult D
                    (real_sum_over_S
                       (fun s : S => real_mult (q s)
                          (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                    (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))))
       (real_opp (real_mult D (real_log Z_align_r Z_align_r_pos)))).
Proof.
  intros q Hq Hnormq.
  set (c := real_mult D (real_log Z_align_r Z_align_r_pos)).
  (* T1：D·(invD·e s) == e s *)
  assert (T1 : forall s : S,
    real_eq (real_mult D (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
            (real_base_loss s)).
  { intro s.
    apply (real_eq_trans
             (real_mult D (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
             (real_mult (real_mult D (real_inv_pos D D_pos)) (real_base_loss s))
             (real_base_loss s)).
    - exact (real_mult_assoc D (real_inv_pos D D_pos) (real_base_loss s)).
    - apply (real_eq_trans
               (real_mult (real_mult D (real_inv_pos D D_pos)) (real_base_loss s))
               (real_mult real_one (real_base_loss s))
               (real_base_loss s)).
      + apply (RealSetoid.real_eq_mult_compat_adapt
                 (real_mult D (real_inv_pos D D_pos)) real_one
                 (real_base_loss s) (real_base_loss s)
                 (real_inv_pos_correct D D_pos) (real_eq_refl _)).
      + apply (real_eq_trans
                 (real_mult real_one (real_base_loss s))
                 (real_mult (real_base_loss s) real_one)
                 (real_base_loss s)).
        * exact (real_mult_comm real_one (real_base_loss s)).
        * exact (real_mult_one (real_base_loss s)). }
  (* T2：D·Lb s == opp (e s + c) *)
  assert (T2 : forall s : S,
    real_eq (real_mult D
               (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                         (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
            (real_opp (real_plus (real_base_loss s) c))).
  { intro s.
    apply (real_eq_trans
             (real_mult D
                (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                          (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
             (real_opp (real_mult D
                          (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                     (real_log Z_align_r Z_align_r_pos))))
             (real_opp (real_plus (real_base_loss s) c))).
    - apply (real_eq_trans
               (real_mult D
                  (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
               (real_mult D
                  (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                       (real_log Z_align_r Z_align_r_pos))))
               (real_opp (real_mult D
                          (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                     (real_log Z_align_r Z_align_r_pos))))).
      + apply (RealSetoid.real_eq_mult_compat_adapt D D _ _ (real_eq_refl D)).
        exact (rfep_boltzmann_log_decomp_real s
                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)).
      + exact (real_mult_opp_l D
                 (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                            (real_log Z_align_r Z_align_r_pos))).
    - apply (RealSetoid.real_eq_opp_compat
               (real_mult D
                  (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                             (real_log Z_align_r Z_align_r_pos)))
               (real_plus (real_base_loss s) c)).
      apply (real_eq_trans
               (real_mult D
                  (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                             (real_log Z_align_r Z_align_r_pos)))
               (real_plus (real_mult D (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                          (real_mult D (real_log Z_align_r Z_align_r_pos)))
               (real_plus (real_base_loss s) c)).
      + exact (real_distrib D (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                            (real_log Z_align_r Z_align_r_pos)).
      + apply (RealSetoid.real_eq_plus_compat_adapt
                 (real_mult D (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                 (real_base_loss s)
                 (real_mult D (real_log Z_align_r Z_align_r_pos))
                 c (T1 s) (real_eq_refl _)). }
  (* T3：e s == opp (D·Lb s) + opp c *)
  assert (T3 : forall s : S,
    real_eq (real_base_loss s)
            (real_plus (real_opp
                          (real_mult D
                             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))
                       (real_opp c))).
  { intro s.
    assert (Haux : real_eq (real_plus (real_base_loss s) c)
                           (real_opp
                              (real_mult D
                                 (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                           (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).
    { apply real_eq_sym.
      apply (real_eq_trans
               (real_opp
                  (real_mult D
                     (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))
               (real_opp (real_opp (real_plus (real_base_loss s) c)))
               (real_plus (real_base_loss s) c)).
      - apply (RealSetoid.real_eq_opp_compat _ _). exact (T2 s).
      - exact (real_opp_opp (real_plus (real_base_loss s) c)). }
    apply (real_eq_trans
             (real_base_loss s)
             (real_plus (real_base_loss s) real_zero)
             (real_plus (real_opp
                           (real_mult D
                              (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                        (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))
                        (real_opp c))).
    apply real_eq_sym. apply real_plus_zero.
    apply (real_eq_trans
             (real_plus (real_base_loss s) real_zero)
             (real_plus (real_plus (real_base_loss s) c) (real_opp c))
             (real_plus (real_opp
                           (real_mult D
                              (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                        (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))
                        (real_opp c))).
    - apply (real_eq_trans
               (real_plus (real_base_loss s) real_zero)
               (real_plus (real_base_loss s) (real_plus c (real_opp c)))
               (real_plus (real_plus (real_base_loss s) c) (real_opp c))).
      + apply (RealSetoid.real_eq_plus_compat_adapt (real_base_loss s) (real_base_loss s)
                 real_zero (real_plus c (real_opp c))
                 (real_eq_refl _)).
        apply real_eq_sym. exact (real_plus_opp c).
      + exact (real_plus_assoc (real_base_loss s) c (real_opp c)).
    - apply (RealSetoid.real_eq_plus_compat_adapt (real_plus (real_base_loss s) c)
               (real_opp
                  (real_mult D
                     (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))
               (real_opp c) (real_opp c)
               Haux (real_eq_refl _)). }
  (* 主链：逐点 ext → sum_add → sum_opp×2 → linear×2 → logZ 常数坍缩 *)
  apply (real_eq_trans
           (real_sum_over_S (fun s : S => real_mult (q s) (real_base_loss s)))
           (real_sum_over_S
              (fun s : S => real_plus
                              (real_opp (real_mult D (real_mult (q s)
                                          (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                                    (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))))
                              (real_opp (real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos))))))
           (real_plus
              (real_opp (real_mult D
                           (real_sum_over_S
                              (fun s : S => real_mult (q s)
                                 (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                           (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))))
              (real_opp (real_mult D (real_log Z_align_r Z_align_r_pos))))).
  - apply real_sum_over_S_ext. intro s.
    (* q·e == q·(opp(D·Lb) + opp c) == opp(D·(q·Lb)) + opp(D·(q·logZ)) *)
    apply (real_eq_trans
             (real_mult (q s) (real_base_loss s))
             (real_mult (q s)
                (real_plus
                   (real_opp
                      (real_mult D
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))
                   (real_opp c)))
             (real_plus
                (real_opp (real_mult D (real_mult (q s)
                             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))))
                (real_opp (real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos)))))).
    + apply (RealSetoid.real_eq_mult_compat_adapt (q s) (q s) _ _ (real_eq_refl (q s)) (T3 s)).
    + apply (real_eq_trans
               (real_mult (q s)
                  (real_plus
                     (real_opp
                        (real_mult D
                           (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                     (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))
                     (real_opp c)))
               (real_plus
                  (real_mult (q s)
                     (real_opp
                        (real_mult D
                           (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                     (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))))
                  (real_mult (q s) (real_opp c)))
               (real_plus
                  (real_opp (real_mult D (real_mult (q s)
                               (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                         (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))))
                  (real_opp (real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos)))))).
      * exact (real_distrib (q s)
                  (real_opp
                     (real_mult D
                        (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                  (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))
                  (real_opp c)).
      * apply (RealSetoid.real_eq_plus_compat_adapt
                 (real_mult (q s)
                    (real_opp
                       (real_mult D
                          (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                    (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))))
                 (real_opp
                    (real_mult D
                       (real_mult (q s)
                          (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                    (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))))
                 (real_mult (q s) (real_opp c))
                 (real_opp (real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos))))).
        -- apply (real_eq_trans
                    (real_mult (q s)
                       (real_opp
                          (real_mult D
                             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))))
                    (real_opp
                       (real_mult (q s)
                          (real_mult D
                             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))))
                    (real_opp
                       (real_mult D
                          (real_mult (q s)
                             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))))).
           ++ exact (real_mult_opp_l (q s)
                        (real_mult D
                           (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                     (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))).
           ++ apply (RealSetoid.real_eq_opp_compat
                       (real_mult (q s)
                          (real_mult D
                             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))
                       (real_mult D
                          (real_mult (q s)
                             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).
              apply (real_eq_trans
                       (real_mult (q s)
                          (real_mult D
                             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))
                       (real_mult (real_mult D (q s))
                          (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                    (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
                       (real_mult D
                          (real_mult (q s)
                             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).
              ** apply (real_eq_trans
                          (real_mult (q s)
                             (real_mult D
                                (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                          (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))
                          (real_mult (real_mult (q s) D)
                             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
                          (real_mult (real_mult D (q s))
                             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))).
                 --- exact (real_mult_assoc (q s) D
                              (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                        (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))).
                 --- apply (RealSetoid.real_eq_mult_compat_adapt (real_mult (q s) D)
                              (real_mult D (q s)) _ _
                              (real_mult_comm (q s) D) (real_eq_refl _)).
              ** apply real_eq_sym.
                 exact (real_mult_assoc D (q s)
                          (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                    (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))).
        -- apply (real_eq_trans
                    (real_mult (q s) (real_opp c))
                    (real_opp (real_mult (q s) c))
                    (real_opp (real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos))))).
           ++ exact (real_mult_opp_l (q s) c).
           ++ apply (RealSetoid.real_eq_opp_compat
                       (real_mult (q s) c)
                       (real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos)))).
              apply (real_eq_trans
                       (real_mult (q s) c)
                       (real_mult (real_mult D (q s)) (real_log Z_align_r Z_align_r_pos))
                       (real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos)))).
              ** apply (real_eq_trans
                          (real_mult (q s) c)
                          (real_mult (real_mult (q s) D) (real_log Z_align_r Z_align_r_pos))
                          (real_mult (real_mult D (q s)) (real_log Z_align_r Z_align_r_pos))).
                 --- exact (real_mult_assoc (q s) D (real_log Z_align_r Z_align_r_pos)).
                 --- apply (RealSetoid.real_eq_mult_compat_adapt (real_mult (q s) D)
                              (real_mult D (q s)) _ _
                              (real_mult_comm (q s) D) (real_eq_refl _)).
              ** apply real_eq_sym.
                 exact (real_mult_assoc D (q s) (real_log Z_align_r Z_align_r_pos)).
  - (* Σ 坍缩：sum_add → sum_opp×2 → linear×2 → logZ 常数（归一化入槽） *)
    apply (real_eq_trans
             (real_sum_over_S
                (fun s : S => real_plus
                                (real_opp (real_mult D (real_mult (q s)
                                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))))
                                (real_opp (real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos))))))
             (real_plus
                (real_opp
                   (real_sum_over_S
                      (fun s : S => real_mult D
                                      (real_mult (q s)
                                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))))
                (real_opp
                   (real_sum_over_S
                      (fun s : S => real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos))))))
             (real_plus
                (real_opp (real_mult D
                             (real_sum_over_S
                                (fun s : S => real_mult (q s)
                                   (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))))
                (real_opp (real_mult D (real_log Z_align_r Z_align_r_pos))))).
    + apply (real_eq_trans
               (real_sum_over_S
                  (fun s : S => real_plus
                                  (real_opp (real_mult D (real_mult (q s)
                                              (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                                        (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))))
                                  (real_opp (real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos))))))
               (real_plus
                  (real_sum_over_S
                     (fun s : S => real_opp
                                     (real_mult D
                                        (real_mult (q s)
                                           (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                                     (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))))
                  (real_sum_over_S
                     (fun s : S => real_opp (real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos))))))
               (real_plus
                  (real_opp
                     (real_sum_over_S
                        (fun s : S => real_mult D
                                        (real_mult (q s)
                                           (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                                     (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))))
                  (real_opp
                     (real_sum_over_S
                        (fun s : S => real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos))))))).
      * exact (real_sum_over_S_add
                 (fun s : S => real_opp
                                 (real_mult D
                                    (real_mult (q s)
                                       (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))))
                 (fun s : S => real_opp (real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos))))).
      * apply (RealSetoid.real_eq_plus_compat_adapt _ _ _ _).
        -- exact (rfep_sum_opp
                    (fun s : S => real_mult D
                                    (real_mult (q s)
                                       (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                                                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).
        -- exact (rfep_sum_opp
                    (fun s : S => real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos)))).
    + apply (RealSetoid.real_eq_plus_compat_adapt _ _ _ _).
      * apply (RealSetoid.real_eq_opp_compat _ _).
        exact (real_sum_over_S_linear D
                 (fun s : S => real_mult (q s)
                    (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                              (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))).
      * apply (RealSetoid.real_eq_opp_compat
                 (real_sum_over_S
                    (fun s : S => real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos))))
                 (real_mult D (real_log Z_align_r Z_align_r_pos))).
        apply (real_eq_trans
                 (real_sum_over_S
                    (fun s : S => real_mult D (real_mult (q s) (real_log Z_align_r Z_align_r_pos))))
                 (real_mult D
                    (real_sum_over_S (fun s : S => real_mult (q s) (real_log Z_align_r Z_align_r_pos))))
                 (real_mult D (real_log Z_align_r Z_align_r_pos))).
        -- exact (real_sum_over_S_linear D
                    (fun s : S => real_mult (q s) (real_log Z_align_r Z_align_r_pos))).
        -- apply (RealSetoid.real_eq_mult_compat_adapt D D _ _ (real_eq_refl D)).
           apply (real_eq_trans
                    (real_sum_over_S (fun s : S => real_mult (q s) (real_log Z_align_r Z_align_r_pos)))
                    (real_mult (real_log Z_align_r Z_align_r_pos) (real_sum_over_S q))
                    (real_log Z_align_r Z_align_r_pos)).
           ++ apply (real_eq_trans
                       (real_sum_over_S (fun s : S => real_mult (q s) (real_log Z_align_r Z_align_r_pos)))
                       (real_sum_over_S (fun s : S => real_mult (real_log Z_align_r Z_align_r_pos) (q s)))
                       (real_mult (real_log Z_align_r Z_align_r_pos) (real_sum_over_S q))).
              ** apply real_sum_over_S_ext. intro s.
                 exact (real_mult_comm (q s) (real_log Z_align_r Z_align_r_pos)).
              ** exact (real_sum_over_S_linear (real_log Z_align_r Z_align_r_pos) q).
           ++ apply (real_eq_trans
                       (real_mult (real_log Z_align_r Z_align_r_pos) (real_sum_over_S q))
                       (real_mult (real_log Z_align_r Z_align_r_pos) real_one)
                       (real_log Z_align_r Z_align_r_pos)).
              ** apply (RealSetoid.real_eq_mult_compat_adapt
                          (real_log Z_align_r Z_align_r_pos) (real_log Z_align_r Z_align_r_pos)
                          (real_sum_over_S q) real_one
                          (real_eq_refl _) Hnormq).
              ** exact (real_mult_one (real_log Z_align_r Z_align_r_pos)).
Qed.

(* ---------------------------------------------------------- *)
(* Part 5：主件——real_kl_decomp_full 槽消解（L43730 / UpRealLeB    *)
(*   L218 同名同型的证明件）：F[p] ≡ F[p_b] + D·Σ kl_term（real_eq，     *)
(*   Σ p=1 前提下零 eps 账目；残留前提仅 Hnormb 一条，件5b 可从          *)
(*   partition 条件供给）                                                *)
(* ---------------------------------------------------------- *)

Lemma rfep_real_kl_decomp_full :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
    (Hnormp : real_eq (real_sum_over_S p) real_one)
    (Hnormb : real_eq (real_sum_over_S
                         (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
                      real_one),
  real_eq
    (real_free_energy S real_sum_over_S real_base_loss D p Hp)
    (real_plus
       (real_free_energy S real_sum_over_S real_base_loss D
          (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
          (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))
       (real_mult D
          (real_sum_over_S
             (fun s : S => real_kl_term (p s)
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                (Hp s)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).
Proof.
  intros p Hp Hnormp Hnormb.
  set (pb := real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (pbpos := real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (Lp := fun s : S => real_log (p s) (Hp s)).
  set (Lb := fun s : S => real_log (pb s) (pbpos s)).
  set (SpLp := real_sum_over_S (fun s : S => real_mult (p s) (Lp s))).
  set (SpLb := real_sum_over_S (fun s : S => real_mult (p s) (Lb s))).
  set (SbLb := real_sum_over_S (fun s : S => real_mult (pb s) (Lb s))).
  set (Spe := real_sum_over_S (fun s : S => real_mult (p s) (real_base_loss s))).
  set (Sbe := real_sum_over_S (fun s : S => real_mult (pb s) (real_base_loss s))).
  set (kllit := real_sum_over_S
                  (fun s : S => real_mult (p s)
                                  (real_plus (Lp s) (real_opp (Lb s))))).
  set (Ksum := real_sum_over_S (fun s : S => real_kl_term (p s) (pb s) (Hp s) (pbpos s))).
  set (c := real_mult D (real_log Z_align_r Z_align_r_pos)).
  (* KCp/KCb：能量期望工作马两例 *)
  assert (KCp : real_eq Spe (real_plus (real_opp (real_mult D SpLb)) (real_opp c))).
  { exact (rfep_energy_expect_eq p Hp Hnormp). }
  assert (KCb : real_eq Sbe (real_plus (real_opp (real_mult D SbLb)) (real_opp c))).
  { exact (rfep_energy_expect_eq pb pbpos Hnormb). }
  (* Hfb：F[p_b] 定义形（Sbe + D·SbLb）== opp c（= −D·log Z，与槽2 结论同值） *)
  assert (Hfb : real_eq (real_plus Sbe (real_mult D SbLb)) (real_opp c)).
  { apply (real_eq_trans
             (real_plus Sbe (real_mult D SbLb))
             (real_plus (real_plus (real_opp (real_mult D SbLb)) (real_opp c))
                        (real_mult D SbLb))
             (real_opp c)).
    - apply (RealSetoid.real_eq_plus_compat_adapt Sbe _ _ _ KCb (real_eq_refl _)).
    - apply (real_eq_trans
               (real_plus (real_plus (real_opp (real_mult D SbLb)) (real_opp c)) (real_mult D SbLb))
               (real_plus (real_plus (real_opp (real_mult D SbLb)) (real_mult D SbLb)) (real_opp c))
               (real_opp c)).
      + (* (opp B + Ct) + B == (opp B + B) + Ct：assoc/comm 重排，B 与 Ct 换位 *)
        apply (real_eq_trans
                 (real_plus (real_plus (real_opp (real_mult D SbLb)) (real_opp c)) (real_mult D SbLb))
                 (real_plus (real_opp (real_mult D SbLb)) (real_plus (real_opp c) (real_mult D SbLb)))
                 (real_plus (real_plus (real_opp (real_mult D SbLb)) (real_mult D SbLb)) (real_opp c))).
        * apply real_eq_sym. exact (real_plus_assoc (real_opp (real_mult D SbLb)) (real_opp c) (real_mult D SbLb)).
        * apply (real_eq_trans
                   (real_plus (real_opp (real_mult D SbLb)) (real_plus (real_opp c) (real_mult D SbLb)))
                   (real_plus (real_opp (real_mult D SbLb)) (real_plus (real_mult D SbLb) (real_opp c)))
                   (real_plus (real_plus (real_opp (real_mult D SbLb)) (real_mult D SbLb)) (real_opp c))).
          -- apply (RealSetoid.real_eq_plus_compat_adapt
                      (real_opp (real_mult D SbLb)) (real_opp (real_mult D SbLb))
                      (real_plus (real_opp c) (real_mult D SbLb))
                      (real_plus (real_mult D SbLb) (real_opp c))
                      (real_eq_refl _) (real_plus_comm (real_opp c) (real_mult D SbLb))).
          -- exact (real_plus_assoc (real_opp (real_mult D SbLb))
                                      (real_mult D SbLb) (real_opp c)).
      + (* (opp B + B) + Ct == Ct：opp B + B == 0 的左零化 + 零加 *)
        apply (real_eq_trans
                 (real_plus (real_plus (real_opp (real_mult D SbLb)) (real_mult D SbLb)) (real_opp c))
                 (real_plus real_zero (real_opp c))
                 (real_opp c)).
        * apply (RealSetoid.real_eq_plus_compat_adapt
                    (real_plus (real_opp (real_mult D SbLb)) (real_mult D SbLb)) real_zero
                    (real_opp c) (real_opp c)
                    (real_eq_trans
                       (real_plus (real_opp (real_mult D SbLb)) (real_mult D SbLb))
                       (real_plus (real_mult D SbLb) (real_opp (real_mult D SbLb)))
                       real_zero
                       (real_eq_sym _ _ (real_plus_comm (real_mult D SbLb) (real_opp (real_mult D SbLb))))
                       (real_plus_opp (real_mult D SbLb)))
                    (real_eq_refl _)).
        * apply (real_eq_trans
                   (real_plus real_zero (real_opp c))
                   (real_plus (real_opp c) real_zero)
                   (real_opp c)).
          -- exact (real_plus_comm real_zero (real_opp c)).
          -- exact (real_plus_zero (real_opp c)). }
  (* KA：Σ kl_literal == SpLp + opp SpLb *)
  assert (KA : real_eq kllit (real_plus SpLp (real_opp SpLb))).
  { apply (real_eq_trans kllit
             (real_plus (real_sum_over_S (fun s : S => real_mult (p s) (Lp s)))
                        (real_sum_over_S (fun s : S => real_opp (real_mult (p s) (Lb s)))))
             (real_plus SpLp (real_opp SpLb))).
    - apply (real_eq_trans kllit
               (real_sum_over_S
                  (fun s : S => real_plus (real_mult (p s) (Lp s))
                                          (real_opp (real_mult (p s) (Lb s)))))
               (real_plus (real_sum_over_S (fun s : S => real_mult (p s) (Lp s)))
                          (real_sum_over_S (fun s : S => real_opp (real_mult (p s) (Lb s)))))).
      + apply real_sum_over_S_ext. intro s.
        apply (real_eq_trans
                 (real_mult (p s) (real_plus (Lp s) (real_opp (Lb s))))
                 (real_plus (real_mult (p s) (Lp s)) (real_mult (p s) (real_opp (Lb s))))
                 (real_plus (real_mult (p s) (Lp s)) (real_opp (real_mult (p s) (Lb s))))).
        * exact (real_distrib (p s) (Lp s) (real_opp (Lb s))).
        * apply (RealSetoid.real_eq_plus_compat_adapt _ _ _ _ (real_eq_refl _)).
          exact (real_mult_opp_l (p s) (Lb s)).
      + exact (real_sum_over_S_add (fun s : S => real_mult (p s) (Lp s))
                  (fun s : S => real_opp (real_mult (p s) (Lb s)))).
    - apply (RealSetoid.real_eq_plus_compat_adapt _ _ _ _ (real_eq_refl _)).
      exact (rfep_sum_opp (fun s : S => real_mult (p s) (Lb s))). }
  (* KB：D·Σ kl_literal == D·SpLp + opp (D·SpLb) *)
  assert (KB : real_eq (real_mult D kllit)
                       (real_plus (real_mult D SpLp) (real_opp (real_mult D SpLb)))).
  { apply (real_eq_trans (real_mult D kllit)
             (real_mult D (real_plus SpLp (real_opp SpLb)))
             (real_plus (real_mult D SpLp) (real_opp (real_mult D SpLb)))).
    - apply (RealSetoid.real_eq_mult_compat_adapt D D _ _ (real_eq_refl D)). exact KA.
    - apply (real_eq_trans
               (real_mult D (real_plus SpLp (real_opp SpLb)))
               (real_plus (real_mult D SpLp) (real_mult D (real_opp SpLb)))
               (real_plus (real_mult D SpLp) (real_opp (real_mult D SpLb)))).
      + exact (real_distrib D SpLp (real_opp SpLb)).
      + apply (RealSetoid.real_eq_plus_compat_adapt _ _ _ _ (real_eq_refl _)).
        exact (real_mult_opp_l D SpLb). }
  (* 主链：F[p] == Spe + D·SpLp == … == F[p_b] + D·Σ kl_term（全 real_eq 链） *)
  apply (real_eq_trans
           (real_free_energy S real_sum_over_S real_base_loss D p Hp)
           (real_plus Spe (real_mult D SpLp))
           (real_plus (real_plus Sbe (real_mult D SbLb)) (real_mult D Ksum))).
  - apply real_eq_refl.
  - apply (real_eq_trans
             (real_plus Spe (real_mult D SpLp))
             (real_plus (real_plus (real_opp (real_mult D SpLb)) (real_opp c)) (real_mult D SpLp))
             (real_plus (real_plus Sbe (real_mult D SbLb)) (real_mult D Ksum))).
    + apply (RealSetoid.real_eq_plus_compat_adapt Spe _ _ _ KCp (real_eq_refl _)).
    + (* 环置换： (A + Ct) + Y == (Y + A) + Ct，A := opp(D·SpLb)，Ct := opp c *)
      apply (real_eq_trans
               (real_plus (real_plus (real_opp (real_mult D SpLb)) (real_opp c)) (real_mult D SpLp))
               (real_plus (real_plus (real_mult D SpLp) (real_opp (real_mult D SpLb))) (real_opp c))
               (real_plus (real_plus Sbe (real_mult D SbLb)) (real_mult D Ksum))).
      * apply (real_eq_trans
                 (real_plus (real_plus (real_opp (real_mult D SpLb)) (real_opp c)) (real_mult D SpLp))
                 (real_plus (real_opp (real_mult D SpLb))
                            (real_plus (real_opp c) (real_mult D SpLp)))
                 (real_plus (real_plus (real_mult D SpLp) (real_opp (real_mult D SpLb))) (real_opp c))).
        -- apply real_eq_sym.
           exact (real_plus_assoc (real_opp (real_mult D SpLb)) (real_opp c) (real_mult D SpLp)).
        -- apply (real_eq_trans
                   (real_plus (real_opp (real_mult D SpLb))
                              (real_plus (real_opp c) (real_mult D SpLp)))
                   (real_plus (real_opp (real_mult D SpLb))
                              (real_plus (real_mult D SpLp) (real_opp c)))
                   (real_plus (real_plus (real_mult D SpLp) (real_opp (real_mult D SpLb)))
                              (real_opp c))).
          ++ apply (RealSetoid.real_eq_plus_compat_adapt
                      (real_opp (real_mult D SpLb)) (real_opp (real_mult D SpLb))
                      (real_plus (real_opp c) (real_mult D SpLp))
                      (real_plus (real_mult D SpLp) (real_opp c))
                      (real_eq_refl _) (real_plus_comm (real_opp c) (real_mult D SpLp))).
          ++ apply (real_eq_trans
                      (real_plus (real_opp (real_mult D SpLb)) (real_plus (real_mult D SpLp) (real_opp c)))
                      (real_plus (real_plus (real_opp (real_mult D SpLb)) (real_mult D SpLp)) (real_opp c))
                      (real_plus (real_plus (real_mult D SpLp) (real_opp (real_mult D SpLb))) (real_opp c))).
          ** exact (real_plus_assoc (real_opp (real_mult D SpLb)) (real_mult D SpLp) (real_opp c)).
          ** apply (RealSetoid.real_eq_plus_compat_adapt
                      (real_plus (real_opp (real_mult D SpLb)) (real_mult D SpLp))
                      (real_plus (real_mult D SpLp) (real_opp (real_mult D SpLb)))
                      (real_opp c) (real_opp c)
                      (real_plus_comm (real_opp (real_mult D SpLb)) (real_mult D SpLp)) (real_eq_refl _)).
      * apply (real_eq_trans
                 (real_plus (real_plus (real_mult D SpLp) (real_opp (real_mult D SpLb))) (real_opp c))
                 (real_plus (real_mult D kllit) (real_opp c))
                 (real_plus (real_plus Sbe (real_mult D SbLb)) (real_mult D Ksum))).
        -- apply (RealSetoid.real_eq_plus_compat_adapt
                    (real_plus (real_mult D SpLp) (real_opp (real_mult D SpLb)))
                    (real_mult D kllit) (real_opp c) (real_opp c)
                    (real_eq_sym _ _ KB) (real_eq_refl _)).
        -- apply (real_eq_trans
                     (real_plus (real_mult D kllit) (real_opp c))
                     (real_plus (real_opp c) (real_mult D Ksum))
                     (real_plus (real_plus Sbe (real_mult D SbLb)) (real_mult D Ksum))).
           ++ apply (real_eq_trans
                       (real_plus (real_mult D kllit) (real_opp c))
                       (real_plus (real_opp c) (real_mult D kllit))
                       (real_plus (real_opp c) (real_mult D Ksum))).
              ** exact (real_plus_comm (real_mult D kllit) (real_opp c)).
              ** apply (RealSetoid.real_eq_plus_compat_adapt
                          (real_opp c) (real_opp c) (real_mult D kllit) (real_mult D Ksum)
                          (real_eq_refl _)).
                 apply (RealSetoid.real_eq_mult_compat_adapt D D _ _ (real_eq_refl D)).
                 apply real_sum_over_S_ext. intro s.
                 apply real_eq_sym.
                 exact (logd_kl_term_minus_form (p s) (pb s) (Hp s) (pbpos s)).
           ++ apply (RealSetoid.real_eq_plus_compat_adapt
                       (real_opp c) (real_plus Sbe (real_mult D SbLb))
                       (real_mult D Ksum) (real_mult D Ksum)
                       (real_eq_sym _ _ Hfb) (real_eq_refl _)).
Qed.

(* ---------------------------------------------------------- *)
(* Part 6：换形桥两件（F 外延 / KL 和第二参外延；全闭合）                *)
(* ---------------------------------------------------------- *)

Lemma rfep_free_energy_ext_r :
  forall (q r : S -> Real) (Hq : forall s : S, real_lt real_zero (q s))
    (Hr : forall s : S, real_lt real_zero (r s)),
  (forall s : S, real_eq (q s) (r s)) ->
  real_eq (real_free_energy S real_sum_over_S real_base_loss D q Hq)
          (real_free_energy S real_sum_over_S real_base_loss D r Hr).
Proof.
  intros q r Hq Hr Hext.
  apply (real_eq_trans
           (real_free_energy S real_sum_over_S real_base_loss D q Hq)
           (real_plus (real_sum_over_S (fun s : S => real_mult (r s) (real_base_loss s)))
                      (real_mult D
                         (real_sum_over_S
                            (fun s : S => real_mult (r s) (real_log (r s) (Hr s))))))
           (real_free_energy S real_sum_over_S real_base_loss D r Hr)).
  - apply (RealSetoid.real_eq_plus_compat_adapt _ _ _ _).
    + apply real_sum_over_S_ext. intro s.
      apply (RealSetoid.real_eq_mult_compat_adapt (q s) (r s)
               (real_base_loss s) (real_base_loss s)
               (Hext s) (real_eq_refl _)).
    + apply (RealSetoid.real_eq_mult_compat_adapt D D _ _ (real_eq_refl D)).
      apply real_sum_over_S_ext. intro s.
      apply (RealSetoid.real_eq_mult_compat_adapt (q s) (r s) _ _ (Hext s)).
      exact (real_log_wd (q s) (r s) (Hq s) (Hr s) (Hext s)).
  - apply real_eq_refl.
Qed.

Lemma rfep_kl_sum_ext_r :
  forall (q r : S -> Real) (Hq : forall s : S, real_lt real_zero (q s))
    (Hr : forall s : S, real_lt real_zero (r s)),
  (forall s : S, real_eq (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s) (r s)) ->
  real_eq
    (real_sum_over_S
       (fun s : S => real_kl_term (q s)
          (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
          (Hq s)
          (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
    (real_sum_over_S (fun s : S => real_kl_term (q s) (r s) (Hq s) (Hr s))).
Proof.
  intros q r Hq Hr Hext.
  apply real_sum_over_S_ext. intro s.
  unfold real_kl_term.
  apply (RealSetoid.real_eq_mult_compat_adapt (q s) (q s) _ _ (real_eq_refl (q s))).
  apply (RealSetoid.real_eq_opp_compat _ _).
  apply (real_log_wd
           (real_mult (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                      (real_inv_pos (q s) (Hq s)))
           (real_mult (r s) (real_inv_pos (q s) (Hq s)))
           (real_mult_positive
              (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
              (real_inv_pos (q s) (Hq s))
              (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
              (real_inv_pos_pos (q s) (Hq s)))
           (real_mult_positive (r s) (real_inv_pos (q s) (Hq s)) (Hr s)
              (real_inv_pos_pos (q s) (Hq s)))
           (RealSetoid.real_eq_mult_compat_adapt
              (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
              (r s)
              (real_inv_pos (q s) (Hq s)) (real_inv_pos (q s) (Hq s))
              (Hext s) (real_eq_refl _))).
Qed.

(* ---------------------------------------------------------- *)

(*   rlhf_free_energy_kl 的 Real 镜像，base=π* 替换）：                  *)
(*   F[π] ≡ F[π*] + D·Σ kl_term(π, π＊)——⑤间隙恒等与⑥唯一性的直接基座   *)
(* ---------------------------------------------------------- *)

Lemma rfep_rlhf_free_energy_kl :
  forall (pi_star : S -> Real) (Hpis : forall s : S, real_lt real_zero (pi_star s))
    (Halign : forall s : S,
                real_eq (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                        (pi_star s))
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
    (Hnormp : real_eq (real_sum_over_S p) real_one)
    (Hnormb : real_eq (real_sum_over_S
                         (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
                      real_one),
  real_eq
    (real_free_energy S real_sum_over_S real_base_loss D p Hp)
    (real_plus
       (real_free_energy S real_sum_over_S real_base_loss D pi_star Hpis)
       (real_mult D
          (real_sum_over_S (fun s : S => real_kl_term (p s) (pi_star s) (Hp s) (Hpis s))))).
Proof.
  intros pi_star Hpis Halign p Hp Hnormp Hnormb.
  apply (real_eq_trans
           (real_free_energy S real_sum_over_S real_base_loss D p Hp)
           (real_plus
              (real_free_energy S real_sum_over_S real_base_loss D
                 (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))
              (real_mult D
                 (real_sum_over_S
                    (fun s : S => real_kl_term (p s)
                       (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                       (Hp s)
                       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))))
           (real_plus
              (real_free_energy S real_sum_over_S real_base_loss D pi_star Hpis)
              (real_mult D
                 (real_sum_over_S (fun s : S => real_kl_term (p s) (pi_star s) (Hp s) (Hpis s)))))).
  - exact (rfep_real_kl_decomp_full p Hp Hnormp Hnormb).
  - apply (RealSetoid.real_eq_plus_compat_adapt _ _ _ _).
    + exact (rfep_free_energy_ext_r
               (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
               pi_star
               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos)
               Hpis Halign).
    + apply (RealSetoid.real_eq_mult_compat_adapt D D _ _ (real_eq_refl D)).
      exact (rfep_kl_sum_ext_r p pi_star Hp Hpis Halign).
Qed.

End RFEPMain.

(* ============================================================ *)
(* G2 关：主件与四假设位件 Print Assumptions（全 Closed 口径）             *)
(* ============================================================ *)
Print Assumptions rfep_real_kl_decomp_full.
Print Assumptions rfep_rlhf_free_energy_kl.
Print Assumptions rfep_kl_term_equiv_real.
Print Assumptions rfep_boltzmann_log_decomp_real.
Print Assumptions rfep_boltzmann_normalized_real.
