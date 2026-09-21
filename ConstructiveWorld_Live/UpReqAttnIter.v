(* ============================================================ *)
(* UpReqAttnIter.v *)
(* *)
(* 目的： 注意力迭代算子的 req 层镜像（核、TV、迭代步）。 *)
(* 主件： attention_iter_i 迭代核与 q_kernel_i；agq_omd_pos / agq_p_norm 正性与范数族。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist、UpReqSampling。 *)
(* 备注： 一温度族载体以 Section 变量承接；迭代正性与 TV 一步界为构造核。 *)
(* ============================================================ *)

(* UpReqAttnIter.v — 签名迁移批 4 清账席：AttentionGibbsBridge q_kernel/收缩迭代簇 req 化
   Id 原件：CW_ConstructiveWorld_219.v Section AttentionGibbsBridge L28817-29330
     （q_kernel 簇 + 段2 TV 收缩核心 + 段3 旗舰 + 几何迭代收敛，25 Lemma/Theorem
      + 1 节参位；边界邻接件 one_minus_delta_pos @28793 顺带已证明）。
   ----------------------------------------------------------------
   核对三源核查结论（防重建，逐件判见头注核对表）：
   1. 首席席 UpReqSampling.v（ReqUContraction 11 件）：领地为 L95737-96039
     Section UContraction——与本簇 Id 行号不同节，但数学同构（通用 u + delta +
     transition + minorization 的两点 TV 收缩机）。本簇收缩脊柱 10 件以出节
     全显投喂实证覆盖：q_kernel_i 等定义件在 u := boltzmann_dist_i、
     nu := 稳态处 δ 透明合一，旗舰 agq_tv_contraction 一行 exact 闭合即脊柱
   2. 余段席 UpReqAttnGibbs.v：冻结清单第 7 条自记“q_kernel/收缩迭代簇
     批0 试点 UpSigMigrate.v 仅 req_attention_is_gibbs_temp（fixed-z 形），
     与本簇零交集。
   真缺件 = 单点对稳态特有件 + 独立辅件 + 收敛旗舰，共 31 件（含节内补建
   新文件 UpReqAttnIter.v（UpReqAttnGibbs.v 已结果稳定，零触碰）。
   ----------------------------------------------------------------
   覆盖核对（req 件名 -> Id 原件 @ 行号；判：已证明=对位消费脊柱件，
   【脊柱 10 件·已已证明（对位消费 UpReqSampling.ReqUContraction 出节件）】
     agq_omd_pos<-28793邻接(对位u_omd_pos_next)
     agq_kernel_nonneg<-28817(对位u_r_nonneg) agq_kernel_row<-28829(对位u_r_norm)
     agq_tr_decomp<-28848(对位u_tr_decomp) agq_delta_absorb<-28874(对位delta_absorb_u)
     agq_step_decomp<-28896(对位u_step_decomp) agq_step_norm<-28931(对位u_step_norm)
     agq_abs_kernel_bound<-29104(对位u_abs_row) agq_iter_norm<-29266(对位u_titer_norm)
     agq_tv_contraction<-29195(旗舰·对位u_tv_contraction两点强于单点 +
       稳态目标端换轨（p_steady_i 槽 + agq_tv_compat_r：step(p) ≡ p 逐点）；
       req 形删非负前提位——同 rsq_u_tv_contraction 判，收缩主界不消费非负位)
   【单点特有 9 件·真证/组装（UpReqSampling 两点机不产出）】
     agq_p_norm<-28802(基带 setoid 件为 Id 形另席结果；本节 sumf 自持重建)
     agq_p_pos<-29012 agq_p_kernel_fixed<-29040(稳态不变性 p·Q==p：
       消费 p_steady 槽 + agq_step_decomp + agq_plus_cancel +
       agq_minus_scal_opp_cc + agq_absorb_inv)
     agq_diff_decomp<-29073(逐点差分解：reqd_minus_compat /
       agq_minus_plus_swap_cc / agq_minus_scal_opp_cc / req_mult_minus_distr_r /
       reqd_sum_minus / req_minus_factor_pt 链) agq_tv_nonneg<-29119
     agq_step_nonneg<-29129 agq_iter_nonneg<-29276 agq_tv_reduce<-29167
     agq_abs_mult_nonneg<-29185
   【独立辅件 6 件·真证（UpReqAlgebra 无同形：req_minus_plus_r 为
     (a-(b+c))==((a-b)-c) 异形；absorb/plus_cancel 无独立件）】
     agq_minus_plus_swap_cc<-28958 agq_minus_scal_opp_cc<-28969
     agq_plus_cancel<-28987 agq_absorb_inv<-29001 agq_omd_le_one<-29022
     agq_omd_lt_one<-29032
   【迭代收敛 4 件】agq_r_pow_dec<-14100接口件特例(κ:=1-δ；真证)
     agq_r_pow_dec_iter<-29251(nat 层 lia/Nat.leb 与 Id 原件同构——Prop 位
       与 Id 原件同阶，先例 UpReqSampling 登记表 7)
     agq_tv_iter<-29287(旗舰2·归纳重放：底 case 数乘单位换轨 + 递归步
       req_le_mult_compat_r 对位；目标端稳态固定，两点 rsq_u_tv_iter 不直接产出)
     agq_iterate_converges<-29330(旗舰3·真证：arch_pow 假设位消解 +
       le_mult_compat_weak + lt_id_l 换序完成)
   【节参位 1】arch_pow_i<-29247(Id r_arch_pow_attn 诚实接口槽逐位保留；
     幂底换 req_r_pow omd，B 类假设位)
   【定义件 δ 同构迁移另计】boltzmann_factor_i<-28592 Z_thermo_i<-28595
     boltzmann_dist_i<-28599(约定不换号：Id boltzmann_factor = exp_neg(1/D·E)
     本节同形) q_kernel_i<-28812(minus→req_minus) attention_step_i<-28789
     inv_two_i<-28782 tv_i<-28785 attention_iter_i(iterate 镜像)。
     Id Variable Z_thermo_pos @28597 → 本节保留 Variable Z_thermo_i_pos
     （Id SumOver 类无 sum_pos 字段，诚实槽逐位）。
   【诚实接口新增（Id 字面 req 同位，先例 ReqStrictOrderBridge L1468/
     UpReqAttnGibbs sum_le 位）】abs_nonneg_h<-Id RealInterface abs_nonneg
     @285 平形（RIS 类仅 eps 形无平形，构造性序不可导→节内假设位，Real 实例
     可满足）；sum_nonneg_h<-Id sum_over_S_nonneg 字段 req 镜像。
   ----------------------------------------------------------------
   纪律：纯构造性；Set 层语句（req/lt/le 均 Set 值；nat 层 (m<=n)%nat 与
   Id 原件同阶）；纯 term-mode（req_trans 链 + compat 桥，无集合oid等价
   实例声明、无 tactic 级改写）；诚实接口假设位逐位保留不放大主张（单点
   化删非负前提位两处已在登记表注明）；全部 coqc/coqchk 经 cpu_guard
   （LoadLimit 60/CoreN 6）。
   ---------------------------------------------------------------- *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSampling.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section ReqAttnIter：q_kernel/收缩迭代簇 req 迁移（29 件）      *)
(*   求和诚实接口 = Id SumOver 类字段（L1400-1441）req 镜像，      *)
(*   节内自持（跨席 Hypothesis 不可消费纪律）。                    *)
(* ============================================================ *)
Section ReqAttnIter.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- 求和诚实接口（Id SumOver 字段 req 镜像，逐位） ---- *)
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
(* 非负函数求和非负（Id sum_over_S_nonneg 字段 req 镜像） *)
Hypothesis sum_nonneg_h :
  forall f : S -> R, (forall s : S, le zero (f s)) -> le zero (sumf f).
(* 求和三角（Id abs_sum_le 字段 req 镜像） *)
Hypothesis abs_sum_le_h :
  forall f : S -> R, le (abs (sumf f)) (sumf (fun s : S => abs (f s))).
(* abs 非负平形（Id RealInterface abs_nonneg @285 req 同位槽：RIS 类仅
   eps 形，构造性序不可导，Real 实例可满足） *)
Hypothesis abs_nonneg_h : forall a : R, le zero (abs a).

(* ---- Boltzmann 侧（Id @28587-28602 镜像；e^{-E/T} 约定不换号） ---- *)
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.

Definition boltzmann_factor_i (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition Z_thermo_i : R := sumf boltzmann_factor_i.

Variable Z_thermo_i_pos : lt zero Z_thermo_i.

Definition boltzmann_dist_i (s : S) : R :=
  mult (inv_pos Z_thermo_i Z_thermo_i_pos) (boltzmann_factor_i s).

(* ---- Markov 侧（Id @28709-28762 镜像；le 层语句同形平迁） ---- *)
Variable transition : S -> S -> R.
(* 行归一（Id transition_normalization @28711；Id->req 出口换轨） *)
Variable transition_row_i :
  forall s : S, req (sumf (fun s' : S => transition s s')) one.
Variable delta : R.
Variable delta_pos : lt zero delta.
Variable delta_lt_one : lt delta one.
(* Doeblin 下界（Id minorization @28759；le 层同形逐位） *)
Variable minorization :
  forall s s' : S, le (mult delta (boltzmann_dist_i s')) (transition s s').
(* 混合 plus 兼容双槽（Id @28761/@28762 同位） *)
Variable lt_plus_compat_lt_le_i :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable lt_plus_compat_le_lt_i :
  forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
(* 双和交换（Id sum_swap_cc @28764 req 形） *)
Variable sum_swap_i : forall f : S -> S -> R,
  req (sumf (fun s : S => sumf (fun s' : S => f s s')))
      (sumf (fun s' : S => sumf (fun s : S => f s s'))).
(* abs 见证位（Id abs_ge_zero_id_cc @28778；出口 Id 换 req，同 UpReqSampling 判） *)
Variable abs_ge_zero_i : forall a : R, le zero a -> req (abs a) a.
(* 稳态（Id steady_state_boltzmann_attn @28722 req 形槽：Id 件由 detailed_balance
   真证且已结果基带 setoid 件；本节自持 B 类假设位逐位保留） *)
Variable p_steady_i :
  forall s' : S,
    req (sumf (fun s : S => mult (boltzmann_dist_i s) (transition s s')))
        (boltzmann_dist_i s').
(* 几何击穿槽（Id r_arch_pow_attn @29247 诚实接口位 req 形；幂底换 req_r_pow） *)
Variable arch_pow_i :
  forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
    sigT (fun N : nat => lt (mult a (req_r_pow (req_minus one delta) N)) eps).

Let omd := req_minus one delta.

(* 1−δ > 0（@28793 边界邻接件顺带已证明；对位消费 rsq_u_omd_pos_next） *)
Lemma agq_omd_pos : lt zero omd.
Proof.
  exact (@rsq_u_omd_pos_next R RIS delta delta_lt_one lt_plus_compat_lt_le_i).
Qed.

Let inv_omd := inv_pos omd agq_omd_pos.

Definition inv_two_i : R := inv_pos (plus one one) req_two_pos.

Definition tv_i (mu nu : S -> R) : R :=
  mult inv_two_i (sumf (fun s : S => abs (req_minus (mu s) (nu s)))).

Definition attention_step_i (mu : S -> R) (s' : S) : R :=
  sumf (fun s : S => mult (mu s) (transition s s')).

(* Q 核（Id q_kernel @28812 req 形）：定义性绑定 = ReqUContraction rsq_u_r_kernel
   全参实例（inv 位见证 proof-relevant，δ 体同构 req (mult inv_omd
   (req_minus (transition s s') (mult delta (boltzmann_dist_i s'))))，
   绑定式避免见证位 conversion 断链——先例 ReqSampling4 k_step 直绑核） *)
Definition q_kernel_i (s s' : S) : R :=
  @rsq_u_r_kernel R RIS S boltzmann_dist_i delta delta_lt_one transition
    lt_plus_compat_lt_le_i s s'.

Fixpoint attention_iter_i (n : nat) (mu : S -> R) : S -> R :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => attention_step_i (attention_iter_i m mu)
  end.

(* ---- 1−δ 余两件（@29022/@29032 真证） ---- *)

(* 1−δ ≤ 1（@29022；真证：aux_delta_plus_omd（UpReqSampling 出节件）+
   req_le_plus_nonneg_r） *)
Lemma agq_omd_le_one : le omd one.
Proof.
  apply (le_id_r omd (plus omd delta) one).
  - exact (req_trans (plus omd delta) (plus delta omd) one
             (plus_comm omd delta) (@aux_delta_plus_omd R RIS delta)).
  - exact (req_le_plus_nonneg_r omd delta (lt_le_iff _ _ (inl delta_pos))).
Qed.

(* 1−δ < 1（@29032；真证：omd δ 展开 + 混合 plus 兼容槽） *)
Lemma agq_omd_lt_one : lt omd one.
Proof.
  exact (lt_id_r omd (plus one zero) one (plus_zero one)
           (lt_plus_compat_le_lt_i one one (opp delta) zero
              (le_refl one) (lt_zero_opp delta delta_pos))).
Qed.

(* ---- 稳态目标两件（@28802/@29012 真证） ---- *)

(* p 归一化（@28802；基带 setoid 件为 Id/SumOver 形，本节 sumf 自持） *)
Lemma agq_p_norm : req (sumf boltzmann_dist_i) one.
Proof.
  unfold boltzmann_dist_i.
  apply (req_trans _ (mult (inv_pos Z_thermo_i Z_thermo_i_pos)
                           (sumf boltzmann_factor_i)) _).
  - exact (sum_linear (inv_pos Z_thermo_i Z_thermo_i_pos) boltzmann_factor_i).
  - exact (req_trans (mult (inv_pos Z_thermo_i Z_thermo_i_pos) Z_thermo_i)
                     (mult Z_thermo_i (inv_pos Z_thermo_i Z_thermo_i_pos)) one
             (mult_comm (inv_pos Z_thermo_i Z_thermo_i_pos) Z_thermo_i)
             (inv_pos_correct Z_thermo_i Z_thermo_i_pos)).
Qed.

(* p 逐点正（@29012；真证：mult_positive 直配） *)
Lemma agq_p_pos : forall s : S, lt zero (boltzmann_dist_i s).
Proof.
  intro s. unfold boltzmann_dist_i.
  apply mult_positive.
  - exact (inv_pos_pos Z_thermo_i Z_thermo_i_pos).
  - unfold boltzmann_factor_i. apply exp_neg_pos.
Qed.

(* ---- 独立代数辅件四件（UpReqAlgebra 无同形，真证） ---- *)

(* 加性消去：a+b==c ⟹ b==c−a（@28987；真证：req_minus_plus_cancel +
   req_add_cancel_l 换序） *)
Lemma agq_plus_cancel :
  forall a b c : R, req (plus a b) c -> req b (req_minus c a).
Proof.
  intros a b c H.
  exact (req_trans _ _ _ (req_sym _ _ (req_minus_plus_cancel_r a b))
           (reqd_minus_compat (plus a b) c a a H (req_refl a))).
Qed.

(* inv 吸收：inv(c)·(c·a)==a（@29001；真证：结合 + inv_pos_correct + 单元） *)
Lemma agq_absorb_inv :
  forall (c : R) (Hc : lt zero c) (a : R),
    req (mult (inv_pos c Hc) (mult c a)) a.
Proof.
  intros c Hc a.
  apply (req_trans (mult (inv_pos c Hc) (mult c a))
                   (mult (mult (inv_pos c Hc) c) a) a).
  - exact (mult_assoc (inv_pos c Hc) c a).
  - apply (req_trans (mult (mult (inv_pos c Hc) c) a) (mult one a) a).
    + exact (req_mult_compat (mult (inv_pos c Hc) c) one a a
               (req_trans (mult (inv_pos c Hc) c)
                          (mult c (inv_pos c Hc)) one
                          (mult_comm (inv_pos c Hc) c)
                          (inv_pos_correct c Hc))
               (req_refl a)).
    + exact (req_mult_one_l a).
Qed.

(* (a+b)−c == b+(a−c)（@28958；真证：结合/交换四步换轨；
   UpReqAlgebra req_minus_plus_r 为 (a−(b+c)) 异形，另建） *)
Lemma agq_minus_plus_swap_cc :
  forall a b c : R, req (req_minus (plus a b) c) (plus b (req_minus a c)).
Proof.
  intros a b c. unfold req_minus.
  apply (req_trans (plus (plus a b) (opp c))
                   (plus a (plus b (opp c))) _).
  - exact (req_sym _ _ (plus_assoc a b (opp c))).
  - apply (req_trans (plus a (plus b (opp c)))
                     (plus a (plus (opp c) b)) _).
    + exact (req_plus_compat a a (plus b (opp c)) (plus (opp c) b)
               (req_refl a) (plus_comm b (opp c))).
    + apply (req_trans (plus a (plus (opp c) b))
                       (plus (plus a (opp c)) b) _).
      * exact (plus_assoc a (opp c) b).
      * exact (plus_comm (plus a (opp c)) b).
Qed.

(* (a·b)−b == −((1−a)·b)（@28969；真证：单元换轨 + 逐点减法因子 + 符号链） *)
Lemma agq_minus_scal_opp_cc :
  forall a b : R,
    req (req_minus (mult a b) b) (opp (mult (req_minus one a) b)).
Proof.
  intros a b.
  assert (Hs : req (req_minus a one) (opp (req_minus one a))).
  { unfold req_minus.
    apply (req_trans (plus a (opp one)) (plus (opp one) a) _).
    - exact (plus_comm a (opp one)).
    - apply (req_trans (plus (opp one) a)
                       (plus (opp one) (opp (opp a))) _).
      + exact (req_plus_compat (opp one) (opp one) a (opp (opp a))
                  (req_refl (opp one)) (req_sym _ _ (req_double_neg a))).
      + exact (req_sym _ _ (req_opp_plus one (opp a))). }
  apply (req_trans (req_minus (mult a b) b)
                   (req_minus (mult a b) (mult one b)) _).
  - exact (reqd_minus_compat (mult a b) (mult a b) b (mult one b)
             (req_refl (mult a b))
             (req_trans _ _ _ (req_sym _ _ (mult_one b)) (mult_comm b one))).
  - apply (req_trans (req_minus (mult a b) (mult one b))
                     (mult (req_minus a one) b) _).
    + exact (req_minus_factor_pt a one b).
    + apply (req_trans (mult (req_minus a one) b)
                       (mult (opp (req_minus one a)) b) _).
      * exact (req_mult_compat (req_minus a one) (opp (req_minus one a))
                  b b Hs (req_refl b)).
      * exact (req_opp_mult_r (req_minus one a) b).
Qed.

(* |c·b| ≤ c·|b|（c ≥ 0）（@29185；真证：abs_mult + abs 见证槽） *)
Lemma agq_abs_mult_nonneg :
  forall a b : R, le zero a -> le (abs (mult a b)) (mult a (abs b)).
Proof.
  intros a b Ha.
  apply (le_id_l (abs (mult a b)) (mult a (abs b)) (mult a (abs b))
                 (req_trans (abs (mult a b)) (mult (abs a) (abs b))
                            (mult a (abs b))
                            (abs_mult a b)
                            (req_mult_compat (abs a) a (abs b) (abs b)
                               (abs_ge_zero_i a Ha) (req_refl (abs b))))
                 (le_refl _)).
Qed.

(* ---- 脊柱十件（对位消费 UpReqSampling.ReqUContraction 出节件；
   u := boltzmann_dist_i，q_kernel_i/attention_step_i/tv_i δ 透明合一） ---- *)

(* Q 核逐点非负（@28817；对位 rsq_u_r_nonneg） *)
Lemma agq_kernel_nonneg : forall s s' : S, le zero (q_kernel_i s s').
Proof.
  intros s s'.
  exact (@rsq_u_r_nonneg R RIS S boltzmann_dist_i delta delta_lt_one transition
           minorization lt_plus_compat_lt_le_i s s').
Qed.

(* Q 核行归一（@28829；对位 rsq_u_r_norm） *)
Lemma agq_kernel_row :
  forall s : S, req (sumf (fun s' : S => q_kernel_i s s')) one.
Proof.
  intro s.
  exact (@rsq_u_r_norm R RIS S sumf sum_ext sum_linear sum_add boltzmann_dist_i
           agq_p_norm delta delta_lt_one transition transition_row_i
           lt_plus_compat_lt_le_i s).
Qed.

(* T == δ·p + (1−δ)·Q（@28848；对位 rsq_u_tr_decomp） *)
Lemma agq_tr_decomp : forall s s' : S,
  req (transition s s')
      (plus (mult delta (boltzmann_dist_i s'))
            (mult omd (q_kernel_i s s'))).
Proof.
  intros s s'.
  exact (@rsq_u_tr_decomp R RIS S boltzmann_dist_i delta delta_lt_one transition
           lt_plus_compat_lt_le_i s s').
Qed.

(* δ·a + (1−δ)·a == a（@28874；对位 rsq_delta_absorb_u） *)
Lemma agq_delta_absorb : forall a : R,
  req (plus (mult delta a) (mult omd a)) a.
Proof.
  intro a. exact (@rsq_delta_absorb_u R RIS delta a).
Qed.

(* 单步分解：Tμ == δ·p + (1−δ)·Qμ（@28896；对位 rsq_u_step_decomp） *)
Lemma agq_step_decomp : forall (mu : S -> R) (s' : S),
  req (sumf mu) one ->
  req (attention_step_i mu s')
      (plus (mult delta (boltzmann_dist_i s'))
            (mult omd (sumf (fun s : S => mult (mu s) (q_kernel_i s s'))))).
Proof.
  intros mu s' Hmu.
  exact (@rsq_u_step_decomp R RIS S sumf sum_ext sum_linear sum_add
           boltzmann_dist_i delta delta_lt_one transition
           lt_plus_compat_lt_le_i mu s' Hmu).
Qed.

(* 单步保持归一化（@28931；对位 rsq_u_step_norm） *)
Lemma agq_step_norm : forall mu : S -> R,
  req (sumf mu) one -> req (sumf (fun s' : S => attention_step_i mu s')) one.
Proof.
  intros mu Hmu.
  exact (@rsq_u_step_norm R RIS S sumf sum_ext sum_linear sum_add boltzmann_dist_i
           agq_p_norm delta delta_lt_one transition transition_row_i
           sum_swap_i lt_plus_compat_lt_le_i mu Hmu).
Qed.

(* |Σ f·Q| ≤ Σ |f|·Q（@29104；对位 rsq_u_abs_row） *)
Lemma agq_abs_kernel_bound : forall (f : S -> R) (s' : S),
  le (abs (sumf (fun s : S => mult (f s) (q_kernel_i s s'))))
     (sumf (fun s : S => mult (abs (f s)) (q_kernel_i s s'))).
Proof.
  intros f s'.
  exact (@rsq_u_abs_row R RIS S sumf sum_ext abs_sum_le_h boltzmann_dist_i delta
           delta_lt_one transition minorization abs_ge_zero_i
           lt_plus_compat_lt_le_i f s').
Qed.

(* 迭代保持归一化（@29266；对位 rsq_u_titer_norm；attention_iter_i 与
   rsq_u_titer 在 transition 合一处 Fixpoint 结构 convertible） *)
Lemma agq_iter_norm : forall (n : nat) (mu : S -> R),
  req (sumf mu) one -> req (sumf (attention_iter_i n mu)) one.
Proof.
  intros n mu Hmu.
  exact (@rsq_u_titer_norm R RIS S sumf sum_ext sum_linear sum_add boltzmann_dist_i
           agq_p_norm delta delta_lt_one transition transition_row_i
           sum_swap_i lt_plus_compat_lt_le_i n mu Hmu).
Qed.

(* tv 右端换轨：nu1 ≡ nu2 逐点 ⟹ tv(f,nu1) == tv(f,nu2)（真证：mult/sum/
   abs/minus 四层 compat） *)
Lemma agq_tv_compat_r : forall (f nu1 nu2 : S -> R),
  (forall s : S, req (nu1 s) (nu2 s)) -> req (tv_i f nu1) (tv_i f nu2).
Proof.
  intros f nu1 nu2 H. unfold tv_i.
  exact (req_mult_compat inv_two_i inv_two_i _ _ (req_refl inv_two_i)
           (sum_ext _ _ (fun s : S =>
              req_abs_compat _ _
                (reqd_minus_compat _ _ _ _ (req_refl _) (H s))))).
Qed.

(* ========== 旗舰 1：单步 TV 收缩（@29195）==========
   对位消费 rsq_u_tv_contraction 两点形于 nu := p + 稳态目标端换轨
   （p_steady_i 槽：step(p) ≡ p 逐点）；req 形删非负前提位——同
   rsq_u_tv_contraction 判。 *)
Lemma agq_tv_contraction : forall mu : S -> R,
  req (sumf mu) one ->
  le (tv_i (attention_step_i mu) boltzmann_dist_i)
     (mult omd (tv_i mu boltzmann_dist_i)).
Proof.
  intros mu Hmu.
  apply (le_id_l _ _ _
           (req_sym _ _
              (agq_tv_compat_r (attention_step_i mu)
                 (attention_step_i boltzmann_dist_i) boltzmann_dist_i
                 p_steady_i))).
  exact (@rsq_u_tv_contraction R RIS S sumf sum_ext sum_linear sum_add sum_le
           abs_sum_le_h boltzmann_dist_i agq_p_norm delta delta_lt_one
           transition transition_row_i minorization sum_swap_i abs_ge_zero_i
           lt_plus_compat_lt_le_i mu boltzmann_dist_i Hmu agq_p_norm).
Qed.

(* ---- 单点特有件（真证/组装） ---- *)

(* 双非负乘法（le·le 弱形；Id le_mult_nonneg_t12 的 req 重建：
   mult_comm + mult_zero 换轨 + le_mult_compat_weak；UpReqAlgebra/UpReqDist
   均无 le·le 现成件，本件节内补建） *)
Lemma agq_le_mult_nonneg :
  forall a b : R, le zero a -> le zero b -> le zero (mult a b).
Proof.
  intros a b Ha Hb.
  apply (le_id_r zero (mult b a) (mult a b) (mult_comm b a)).
  apply (le_id_l zero (mult zero a) (mult b a)).
  - exact (req_sym (mult zero a) zero
             (req_trans (mult zero a) (mult a zero) zero
                        (mult_comm zero a) (mult_zero a))).
  - exact (le_mult_compat_weak zero b a Ha Hb).
Qed.

(* 单步保持非负（@29129；真证：X/Y 双腿 + le_plus_compat） *)
Lemma agq_step_nonneg : forall mu : S -> R,
  req (sumf mu) one -> (forall s : S, le zero (mu s)) ->
  forall s' : S, le zero (attention_step_i mu s').
Proof.
  intros mu Hmu Hnn s'.
  assert (HX : le zero (mult delta (boltzmann_dist_i s'))).
  { apply (aux_le_mult_nonneg_t12 delta (boltzmann_dist_i s')).
    - exact delta_pos.
    - exact (lt_le_iff _ _ (inl (agq_p_pos s'))). }
  assert (HY : le zero (mult omd (sumf (fun s : S =>
                  mult (mu s) (q_kernel_i s s'))))).
  { apply (aux_le_mult_nonneg_t12 omd
              (sumf (fun s : S => mult (mu s) (q_kernel_i s s')))).
    - exact agq_omd_pos.
    - apply sum_nonneg_h. intro s.
      exact (agq_le_mult_nonneg (mu s) (q_kernel_i s s')
               (Hnn s) (agq_kernel_nonneg s s')). }
  assert (Hstep : le zero (plus (mult delta (boltzmann_dist_i s'))
                                (mult omd (sumf (fun s : S =>
                                   mult (mu s) (q_kernel_i s s')))))).
  { apply (le_id_l zero (plus zero zero) _ (req_sym _ _ (plus_zero zero))).
    exact (le_plus_compat zero (mult delta (boltzmann_dist_i s')) zero
             (mult omd (sumf (fun s : S => mult (mu s) (q_kernel_i s s'))))
             HX HY). }
  apply (le_id_r zero (plus (mult delta (boltzmann_dist_i s'))
                            (mult omd (sumf (fun s : S =>
                               mult (mu s) (q_kernel_i s s')))))
                   (attention_step_i mu s')).
  - exact (req_sym _ _ (agq_step_decomp mu s' Hmu)).
  - exact Hstep.
Qed.

(* 迭代保持非负（@29276；真证：单点非负位归纳） *)
Lemma agq_iter_nonneg : forall (n : nat) (mu : S -> R),
  req (sumf mu) one -> (forall s : S, le zero (mu s)) ->
  forall s : S, le zero (attention_iter_i n mu s).
Proof.
  intro n. induction n as [| n IH]; intros mu Hmu Hnn s.
  - exact (Hnn s).
  - exact (agq_step_nonneg (attention_iter_i n mu)
             (agq_iter_norm n mu Hmu) (IH mu Hmu Hnn) s).
Qed.

(* 稳态不变性：p·Q == p（@29040；真证：p_steady 槽 + 单步分解 +
   agq_plus_cancel + agq_minus_scal_opp_cc + agq_absorb_inv） *)
Lemma agq_p_kernel_fixed : forall s' : S,
  req (sumf (fun s : S => mult (boltzmann_dist_i s) (q_kernel_i s s')))
      (boltzmann_dist_i s').
Proof.
  intro s'.
  assert (H3 : req (plus (mult delta (boltzmann_dist_i s'))
                         (mult omd (sumf (fun s : S =>
                            mult (boltzmann_dist_i s) (q_kernel_i s s')))))
                   (boltzmann_dist_i s')).
  { exact (req_trans _ _ _
             (req_sym _ _ (agq_step_decomp boltzmann_dist_i s' agq_p_norm))
             (p_steady_i s')). }
  assert (H7 : req (mult omd (sumf (fun s : S =>
                      mult (boltzmann_dist_i s) (q_kernel_i s s'))))
                   (mult omd (boltzmann_dist_i s'))).
  { assert (H4 : req (mult omd (sumf (fun s : S =>
                        mult (boltzmann_dist_i s) (q_kernel_i s s'))))
                     (req_minus (boltzmann_dist_i s')
                                (mult delta (boltzmann_dist_i s'))))
      by exact (agq_plus_cancel (mult delta (boltzmann_dist_i s')) _
                  (boltzmann_dist_i s') H3).
    assert (H6 : req (req_minus (boltzmann_dist_i s')
                                (mult delta (boltzmann_dist_i s')))
                     (mult omd (boltzmann_dist_i s'))).
    { apply (req_trans _ (req_minus (mult one (boltzmann_dist_i s'))
                                    (mult delta (boltzmann_dist_i s'))) _).
      - exact (reqd_minus_compat (boltzmann_dist_i s')
                  (mult one (boltzmann_dist_i s'))
                  (mult delta (boltzmann_dist_i s'))
                  (mult delta (boltzmann_dist_i s'))
                  (req_trans _ _ _
                     (req_sym _ _ (mult_one (boltzmann_dist_i s')))
                     (mult_comm (boltzmann_dist_i s') one))
                  (req_refl _)).
      - exact (req_sym _ _ (req_mult_minus_distr_r one delta
                  (boltzmann_dist_i s'))). }
    exact (req_trans _ _ _ H4 H6). }
  assert (HA : req (mult inv_omd (mult omd (sumf (fun s : S =>
                      mult (boltzmann_dist_i s) (q_kernel_i s s')))))
                   (sumf (fun s : S =>
                      mult (boltzmann_dist_i s) (q_kernel_i s s'))))
    by exact (agq_absorb_inv omd agq_omd_pos
                (sumf (fun s : S => mult (boltzmann_dist_i s) (q_kernel_i s s')))).
  assert (HC : req (mult inv_omd (mult omd (boltzmann_dist_i s')))
                   (boltzmann_dist_i s'))
    by exact (agq_absorb_inv omd agq_omd_pos (boltzmann_dist_i s')).
  apply (req_trans _ (mult inv_omd (mult omd (sumf (fun s : S =>
         mult (boltzmann_dist_i s) (q_kernel_i s s'))))) _).
  - exact (req_sym _ _ HA).
  - apply (req_trans _ (mult inv_omd (mult omd (boltzmann_dist_i s'))) _).
    + exact (req_mult_compat _ _ _ _ (req_refl _) H7).
    + exact HC.
Qed.

(* 逐点差分解：Tμ−p == (1−δ)·Σ(μ−p)·Q（@29073；真证：reqd_minus_compat +
   agq_minus_plus_swap_cc + agq_minus_scal_opp_cc + req_mult_minus_distr_r +
   agq_p_kernel_fixed + reqd_sum_minus + req_minus_factor_pt 链） *)
Lemma agq_diff_decomp : forall (mu : S -> R) (s' : S),
  req (sumf mu) one ->
  req (req_minus (attention_step_i mu s') (boltzmann_dist_i s'))
      (mult omd
            (sumf (fun s : S =>
               mult (req_minus (mu s) (boltzmann_dist_i s))
                    (q_kernel_i s s')))).
Proof.
  intros mu s' Hmu.
  assert (S1 : req (req_minus (attention_step_i mu s') (boltzmann_dist_i s'))
                   (req_minus (plus (mult delta (boltzmann_dist_i s'))
                                    (mult omd (sumf (fun s : S =>
                                       mult (mu s) (q_kernel_i s s')))))
                              (boltzmann_dist_i s')))
    by exact (reqd_minus_compat (attention_step_i mu s')
                (plus (mult delta (boltzmann_dist_i s'))
                      (mult omd (sumf (fun s : S =>
                         mult (mu s) (q_kernel_i s s')))))
                (boltzmann_dist_i s') (boltzmann_dist_i s')
                (agq_step_decomp mu s' Hmu) (req_refl _)).
  assert (S23 : req (req_minus (plus (mult delta (boltzmann_dist_i s'))
                                     (mult omd (sumf (fun s : S =>
                                        mult (mu s) (q_kernel_i s s')))))
                                (boltzmann_dist_i s'))
                   (plus (mult omd (sumf (fun s : S =>
                            mult (mu s) (q_kernel_i s s'))))
                         (opp (mult omd (boltzmann_dist_i s'))))).
  { apply (req_trans _ _ _
             (agq_minus_plus_swap_cc (mult delta (boltzmann_dist_i s'))
                (mult omd (sumf (fun s : S => mult (mu s) (q_kernel_i s s'))))
                (boltzmann_dist_i s'))).
    exact (req_plus_compat _ _ _ _ (req_refl _)
             (agq_minus_scal_opp_cc delta (boltzmann_dist_i s'))). }
  assert (S4 : req (req_minus (mult omd (sumf (fun s : S =>
                                  mult (mu s) (q_kernel_i s s'))))
                              (mult omd (boltzmann_dist_i s')))
                   (mult omd (req_minus (sumf (fun s : S =>
                                           mult (mu s) (q_kernel_i s s')))
                                        (boltzmann_dist_i s'))))
    by exact (req_sym _ _ (req_mult_minus_distr_l omd
                (sumf (fun s : S => mult (mu s) (q_kernel_i s s')))
                (boltzmann_dist_i s'))).
  assert (S5 : req (req_minus (sumf (fun s : S =>
                                  mult (mu s) (q_kernel_i s s')))
                              (boltzmann_dist_i s'))
                   (sumf (fun s : S =>
                      mult (req_minus (mu s) (boltzmann_dist_i s))
                           (q_kernel_i s s')))).
  { apply (req_trans _ (req_minus
           (sumf (fun s : S => mult (mu s) (q_kernel_i s s')))
           (sumf (fun s : S => mult (boltzmann_dist_i s) (q_kernel_i s s')))) _).
    - exact (reqd_minus_compat (sumf (fun s : S =>
                  mult (mu s) (q_kernel_i s s')))
                  (sumf (fun s : S =>
                     mult (mu s) (q_kernel_i s s')))
                  (boltzmann_dist_i s')
                  (sumf (fun s : S =>
                     mult (boltzmann_dist_i s) (q_kernel_i s s')))
                  (req_refl _)
                  (req_sym _ _ (agq_p_kernel_fixed s'))).
    - apply (req_trans _ (sumf (fun s : S =>
           req_minus (mult (mu s) (q_kernel_i s s'))
                     (mult (boltzmann_dist_i s) (q_kernel_i s s')))) _).
      + exact (req_sym _ _
                   (@reqd_sum_minus R RIS S sumf sum_ext sum_add sum_linear
                      (fun s : S => mult (mu s) (q_kernel_i s s'))
                      (fun s : S =>
                         mult (boltzmann_dist_i s) (q_kernel_i s s')))).
      + apply (sum_ext _ _).
        intro s. exact (req_minus_factor_pt (mu s) (boltzmann_dist_i s)
                          (q_kernel_i s s')). }
  apply (req_trans _ _ _ S1
           (req_trans _ _ _ S23
              (req_trans _ _ _ S4
                 (req_mult_compat _ _ _ _ (req_refl _) S5)))).
Qed.

(* TV 距离非负（@29119；真证：inv 双正 + sum_nonneg_h + abs_nonneg_h 槽） *)
Lemma agq_tv_nonneg : forall mu nu : S -> R, le zero (tv_i mu nu).
Proof.
  intros mu nu. unfold tv_i.
  apply (aux_le_mult_nonneg_t12 inv_two_i
            (sumf (fun s : S => abs (req_minus (mu s) (nu s))))).
  - exact (inv_pos_pos (plus one one) req_two_pos).
  - apply sum_nonneg_h. intro s.
    exact (abs_nonneg_h (req_minus (mu s) (nu s))).
Qed.

(* 双和归约：(1/2)·Σ_{s'}(1−δ)·Σ_s f·Q == (1−δ)·(1/2)·Σ f（@29167；
   组装：sum_linear + sum_swap_i + 行归一逐点完成 + 结合换序） *)
Lemma agq_tv_reduce : forall f : S -> R,
  req (mult inv_two_i (sumf (fun s' : S => mult omd
         (sumf (fun s : S => mult (f s) (q_kernel_i s s'))))))
      (mult omd (mult inv_two_i (sumf f))).
Proof.
  intro f.
  apply (req_trans _ (mult inv_two_i (mult omd
         (sumf (fun s' : S => sumf (fun s : S =>
            mult (f s) (q_kernel_i s s')))))) _).
  - exact (req_mult_compat inv_two_i inv_two_i _ _ (req_refl inv_two_i)
             (sum_linear omd (fun s' : S =>
                sumf (fun s : S => mult (f s) (q_kernel_i s s'))))).
  - apply (req_trans _ (mult inv_two_i (mult omd
           (sumf (fun s : S => sumf (fun s' : S =>
              mult (f s) (q_kernel_i s s')))))) _).
    + exact (req_mult_compat inv_two_i inv_two_i _ _ (req_refl inv_two_i)
               (req_mult_compat omd omd _ _ (req_refl omd)
                  (req_sym _ _ (sum_swap_i (fun s s' : S =>
                     mult (f s) (q_kernel_i s s')))))).
    + assert (Hpt : forall s : S,
               req (sumf (fun s' : S => mult (f s) (q_kernel_i s s'))) (f s)).
      { intro s.
        apply (req_trans _ (mult (f s) (sumf (fun s' : S => q_kernel_i s s')))).
        - exact (sum_linear (f s) (fun s' : S => q_kernel_i s s')).
        - apply (req_trans _ (mult (f s) one)).
          + exact (req_mult_compat (f s) (f s)
                     (sumf (fun s' : S => q_kernel_i s s')) one
                     (req_refl (f s)) (agq_kernel_row s)).
          + exact (mult_one (f s)). }
      assert (Hsum : req (sumf (fun s : S =>
                          sumf (fun s' : S => mult (f s) (q_kernel_i s s'))))
                         (sumf f))
        by exact (sum_ext _ _ Hpt).
      apply (req_trans _ (mult inv_two_i (mult omd (sumf f))) _).
      * exact (req_mult_compat inv_two_i inv_two_i _ _ (req_refl inv_two_i)
                  (req_mult_compat omd omd _ _ (req_refl omd) Hsum)).
      * exact (req_trans (mult inv_two_i (mult omd (sumf f)))
                  (mult (mult inv_two_i omd) (sumf f))
                  (mult omd (mult inv_two_i (sumf f)))
                  (mult_assoc inv_two_i omd (sumf f))
                  (req_trans (mult (mult inv_two_i omd) (sumf f))
                     (mult (mult omd inv_two_i) (sumf f))
                     (mult omd (mult inv_two_i (sumf f)))
                     (req_mult_compat (mult inv_two_i omd) (mult omd inv_two_i)
                        (sumf f) (sumf f)
                        (mult_comm inv_two_i omd) (req_refl (sumf f)))
                     (req_sym _ _ (mult_assoc omd inv_two_i (sumf f))))).

Qed.

(* ---- 幂单调与几何迭代 ---- *)

(* 幂递减步：omd^{S n} ≤ omd^n（Id r_pow_dec @14100 特例 κ:=1−δ；真证：
   底 case 单元换轨 + 递归步 le_mult_compat；UpReqSampling req_r_pow 无
   单调件，本件补建） *)
Lemma agq_r_pow_dec : forall n : nat,
  le (req_r_pow omd (Datatypes.S n)) (req_r_pow omd n).
Proof.
  intro n. induction n as [| m IH].
  - exact (le_id_l (mult omd one) omd one (mult_one omd) agq_omd_le_one).
  - apply (le_id_l _ (mult (req_r_pow omd (Datatypes.S m)) omd) _).
    + exact (mult_comm omd (req_r_pow omd (Datatypes.S m))).
    + apply (le_id_r _ (mult (req_r_pow omd m) omd) _).
      * exact (mult_comm (req_r_pow omd m) omd).
      * apply (le_mult_compat _ _ _ agq_omd_pos).
        exact IH.
Qed.

(* 幂指数递减：m ≤ n ⟹ omd^n ≤ omd^m（@29251；组装：nat 层 lia/Nat.leb
   与 Id 原件同构（Prop 位与 Id 原件同阶）+ agq_r_pow_dec） *)
Lemma agq_r_pow_dec_iter : forall m n : nat,
  (m <= n)%nat -> le (req_r_pow omd n) (req_r_pow omd m).
Proof.
  intros m n Hmn. revert m Hmn.
  induction n as [| n IH]; intros m Hmn.
  - assert (Hm0 : m = 0%nat) by lia. subst m. apply le_refl.
  - destruct (Nat.leb m n) eqn:Emn.
    + apply (le_trans _ (req_r_pow omd n) _).
      * exact (agq_r_pow_dec n).
      * exact (IH m (proj1 (PeanoNat.Nat.leb_le m n) Emn)).
    + apply PeanoNat.Nat.leb_gt in Emn.
      assert (Hm : m = Datatypes.S n) by lia. subst m. apply le_refl.
Qed.

(* ========== 旗舰 2：几何迭代 TV 收缩（@29287）==========
   真证归纳：底 case 数乘单位换轨；递归步 agq_tv_contraction +
   req_le_mult_compat_r + 结合换轨；目标端稳态固定。 *)
Lemma agq_tv_iter : forall (n : nat) (mu : S -> R),
  req (sumf mu) one ->
  le (tv_i (attention_iter_i n mu) boltzmann_dist_i)
     (mult (req_r_pow omd n) (tv_i mu boltzmann_dist_i)).
Proof.
  intro n. induction n as [| n IH]; intros mu Hmu.
  - exact (le_id_l _ _ _
             (req_trans _ _ _
                (req_sym _ _ (mult_one (tv_i mu boltzmann_dist_i)))
                (mult_comm (tv_i mu boltzmann_dist_i) one))
             (le_refl _)).
  - assert (Hn : req (sumf (attention_iter_i n mu)) one)
      by exact (agq_iter_norm n mu Hmu).
    assert (Hge : le zero omd)
      by exact (req_le_minus_nonneg delta one
                  (lt_le_iff _ _ (inl delta_lt_one))).
    apply (le_trans _ (mult omd
             (tv_i (attention_iter_i n mu) boltzmann_dist_i)) _).
    + apply (le_id_l _ (tv_i (attention_step_i (attention_iter_i n mu))
                             boltzmann_dist_i) _).
      * exact (req_refl (tv_i (attention_step_i (attention_iter_i n mu))
                              boltzmann_dist_i)).
      * exact (agq_tv_contraction (attention_iter_i n mu) Hn).
    + apply (le_trans _ (mult omd
             (mult (req_r_pow omd n) (tv_i mu boltzmann_dist_i))) _).
      * exact (req_le_mult_compat_r omd
                  (tv_i (attention_iter_i n mu) boltzmann_dist_i)
                  (mult (req_r_pow omd n) (tv_i mu boltzmann_dist_i))
                  Hge (IH mu Hmu)).
      * apply (le_id_l _ (mult (mult omd (req_r_pow omd n))
                               (tv_i mu boltzmann_dist_i))).
        -- exact (mult_assoc omd (req_r_pow omd n)
                              (tv_i mu boltzmann_dist_i)).
        -- apply le_refl.
Qed.

(* ========== 旗舰 3：迭代收敛（@29330）==========
   真证：arch_pow_i 假设位消解 + agq_tv_iter + agq_tv_nonneg +
   agq_r_pow_dec_iter + le_mult_compat_weak + lt_id_l 换序完成；
   req 形删初态非负前提位（agq_tv_iter 链不消费，同旗舰 1 判）。 *)
Theorem agq_iterate_converges :
  forall mu0 : S -> R,
    req (sumf mu0) one ->
    forall eps : R, lt zero eps ->
      lt zero (tv_i mu0 boltzmann_dist_i) ->
      sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
        lt (tv_i (attention_iter_i n mu0) boltzmann_dist_i) eps).
Proof.
  intros mu0 Hmu eps Hep Htv0.
  destruct (arch_pow_i (tv_i mu0 boltzmann_dist_i) Htv0 eps Hep) as [N HN].
  exists N. intros n Hn.
  apply (le_lt_trans _ (mult (req_r_pow omd n)
                             (tv_i mu0 boltzmann_dist_i)) _).
  - exact (agq_tv_iter n mu0 Hmu).
  - apply (le_lt_trans _ (mult (req_r_pow omd N)
                               (tv_i mu0 boltzmann_dist_i)) _).
    + apply (le_mult_compat_weak _ _ _).
      * exact (agq_tv_nonneg mu0 boltzmann_dist_i).
      * exact (agq_r_pow_dec_iter N n Hn).
    + exact (lt_id_l _ _ _
               (mult_comm (req_r_pow omd N) (tv_i mu0 boltzmann_dist_i))
               HN).
Qed.

End ReqAttnIter.
Print Assumptions agq_omd_lt_one.
