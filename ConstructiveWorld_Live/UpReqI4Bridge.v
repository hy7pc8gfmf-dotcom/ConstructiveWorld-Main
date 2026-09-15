(* ============================================================ *)
(* UpReqI4Bridge.v *)
(* *)
(* 目的： 结论 I4 消费位的对接桥（KL 幂单调 B 形）。 *)
(* 主件： i4b_policy_iter_kl_pow_mono_B 及其 eq0 形：KL 幂单调的策略迭代版本。 *)
(* 依赖： CW_ConstructiveWorld_219、UpRealLeB、UpRealLeB2、G07_KLWall、UpReqGeomD、UpGeomB、UpReqGeomIter、UpReqPowMonoBridge。 *)
(* 备注： 证书位形态以诚实登记表申报（见尾注）；幂单调取 ≤_B 显式形。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqI4Bridge.v —— 结论 I4 消费位对接正式落件席 T20                     *)
(*   任务书源＝X3d 结果链：UpReqPowMonoBridge.v（④ le_b 乘法保序闭包      *)
(*   合成器族，6 件全 Qed）＋ 对接草案 _x3d_I4BridgeCheck.v（一跳验证     *)

(*   改名规范化（i4b_ 前缀）、头注逐件登记表、逐件 Qed，并把残差单点        *)
(*   升级为「证书位接口」：两支可通行支路登记在案，缺口形状如实注记。     *)
(* ---------------------------------------------------------------- *)
(* 对接链（草案同款，两跳 trans）：                                       *)
(*   ① geodi_policy_iter_kl_geom_iter_B（UpReqGeomIter 主件 B 伴件）      *)
(*      ：KL_{t1} ≤_B κ^{t1}·KL_0；                                       *)
(*   ② ④∘③：x3d_le_b_mult_r_nonneg_or（UpReqPowMonoBridge 件1，非负      *)
(*      右因子取 KL_0）× powb_one_minus_eta_mono_dec（G07_KLWall）        *)
(*      ：κ^{t1}·KL_0 ≤_B κ^t·KL_0；                                      *)
(*   经 UpRealLeB2 real_le_b_trans ⟹ 结论 I4 目标形                      *)
(*      「t ≤ t1 ⟹ KL_{t1} ≤_B κ^t·KL_0」。                               *)
(* ---------------------------------------------------------------- *)
(* 证书位形态（诚实登记表，详见尾注）：                                     *)
(*   残差＝Or 形 0 ≤ KL_0 证书（real_le = lt ∨ eq，Set 值）。两支可通行： *)
(*   · lt 支：0 < KL_0 严格见证 → Or 左支直供（件0a）；                   *)
(*   · eq 支：KL_0 == 0 → 等式反射运输（件0b）。                          *)
(*   B 形 0 ≤_B KL_0（geodi_kl_nonneg_B / real_gibbs_inequality_B）不     *)

(* ---------------------------------------------------------------- *)
(* 件清单：                                                               *)
(*   件0a i4b_kl0_or_of_lt：严格见证支 Or 证书构造；                      *)
(*   件0b i4b_kl0_or_of_eq：等式反射支 Or 证书构造；                      *)
(*   件1 i4b_pow_kl_mono_le_b：结论 I4 尾注所指缺口形状的实例闭合         *)
(*      （κ^{t1}·KL_0 ≤_B κ^t·KL_0；④∘③ 在消费点直连）；                 *)
(*   件2 i4b_policy_iter_kl_pow_mono_B：主桥（结论 I4 消费位对接件，      *)
(*      X3d 草案 x3d_i4_bridge_draft 正式化；补充 Hkl0or 前提下闭合）；   *)
(*   件3 i4b_policy_iter_kl_pow_mono_eq0：eq 支证书端到端闭合实例         *)
(*      （主件包＋KL_0==0 见证 ⟹ 结论 I4 目标形无条件成立）。             *)
(* ---------------------------------------------------------------- *)
(* 红线自检：零未闭合证明（全 Qed）；零新依赖面（仅 Require 既有绿库）；  *)
(*   语句面全 Set 值（real_le_b/real_le/real_lt/real_eq 全 Set 值，       *)
(*   Or:=A+B 库内定义）；纯 term-mode 组装（real_eq 非 Id 禁改写，全链    *)
(*   real_eq_trans/RealSetoid 运输族）；禁词全零（按全文件计含头注）。    *)
(* 编译配方（vo 树前置；EMPTY 处实为空串实参，引号从略防注释串警告；      *)
(*   cpu_guard 包装零裸调，CoreN 2；先 -vos 秒审再全量）：                *)

(* ============================================================ *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import G07_KLWall.
Require Import UpReqGeomD.
Require Import UpGeomB.
Require Import UpReqGeomIter.
Require Import UpReqPowMonoBridge.

(* ============================================================ *)
(* 〇、证书位接口：Or 形 0 ≤ KL_0 的两支可通行构造                        *)
(* ============================================================ *)

(* 件0a：严格见证支。0 < KL_0 直接给 Or 左支（real_le = lt ∨ eq）。 *)
Lemma i4b_kl0_or_of_lt : forall KL0 : Real,
  real_lt real_zero KL0 -> real_le real_zero KL0.
Proof.
  intros KL0 H. exact (inl H).
Qed.

(* 件0b：等式反射支。KL_0 == 0 经 real_eq_sym 运输＋Or 右支自反。 *)
Lemma i4b_kl0_or_of_eq : forall KL0 : Real,
  real_eq KL0 real_zero -> real_le real_zero KL0.
Proof.
  intros KL0 Heq.
  exact (RealSetoid.real_le_id_l real_zero KL0 KL0
           (real_eq_sym KL0 real_zero Heq) (real_le_refl KL0)).
Qed.

(* ============================================================ *)
(* 一、结论 I4 缺口形状实例闭合：κ^{t1}·KL_0 ≤_B κ^t·KL_0                 *)
(*   ＝ UpReqGeomIter 尾注所指「κ^{t1}·KL_0 ≤ κ^t·KL_0+δ 的 le_b 乘法    *)
(*   保序闭包（非负右因子版）」在消费点的单点落成（④件1 ∘ ③powb 单调）。 *)
(* ============================================================ *)

Lemma i4b_pow_kl_mono_le_b : forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (t t1 : nat) (Hle : NatLe t t1),
  real_le real_zero
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i) (p i) (Hr i) (Hp i))) ->
  real_le_b
    (real_mult (powb_pow (real_plus real_one (real_opp eta)) t1)
               (geod_lsum n (fun i : nat =>
                  real_kl_term (r i) (p i) (Hr i) (Hp i))))
    (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
               (geod_lsum n (fun i : nat =>
                  real_kl_term (r i) (p i) (Hr i) (Hp i)))).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp t t1 Hle Hkl0or.
  exact (x3d_le_b_mult_r_nonneg_or
           (powb_pow (real_plus real_one (real_opp eta)) t1)
           (powb_pow (real_plus real_one (real_opp eta)) t)
           (geod_lsum n (fun i : nat =>
              real_kl_term (r i) (p i) (Hr i) (Hp i)))
           (powb_one_minus_eta_mono_dec eta t t1 Heta Hlt1 Hle)
           Hkl0or).
Qed.

(* ============================================================ *)
(* 二、主桥：结论 I4 消费位对接件（X3d 草案 x3d_i4_bridge_draft 正式化）  *)
(* ============================================================ *)

Lemma i4b_policy_iter_kl_pow_mono_B :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (Hkl0or : real_le real_zero
                (geod_lsum n (fun i : nat =>
                   real_kl_term (r i) (p i) (Hr i) (Hp i))))
    (t t1 : nat) (Hle : NatLe t t1),
  real_le_b
    (geod_lsum n (fun i : nat =>
        real_kl_term (r i)
          (geodi_iterate n r Hr eta p Hp Hn t1 i)
          (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t1 i)))
    (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
               (geod_lsum n (fun i : nat =>
                  real_kl_term (r i) (p i) (Hr i) (Hp i)))).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn Hkl0or t t1 Hle.
  apply (real_le_b_trans
           (geod_lsum n (fun i : nat =>
              real_kl_term (r i)
                (geodi_iterate n r Hr eta p Hp Hn t1 i)
                (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t1 i)))
           (real_mult (powb_pow (real_plus real_one (real_opp eta)) t1)
              (geod_lsum n (fun i : nat =>
                 real_kl_term (r i) (p i) (Hr i) (Hp i))))
           (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
              (geod_lsum n (fun i : nat =>
                 real_kl_term (r i) (p i) (Hr i) (Hp i))))).
  (* 跳①：主件 B 伴件（t1 站位，UpReqGeomIter 旗舰伴件） *)
  - exact (geodi_policy_iter_kl_geom_iter_B n r Hr eta Heta Hlt1 p Hp
             Hnormr Hnormp Hn t1).
  (* 跳②：件1（④∘③，非负右因子取 KL_0） *)
  - exact (i4b_pow_kl_mono_le_b n r Hr eta Heta Hlt1 p Hp t t1 Hle Hkl0or).
Qed.

(* ============================================================ *)
(* 三、证书支路实例：eq 支端到端闭合（证书位接口消费演示）                *)
(* ============================================================ *)

Lemma i4b_policy_iter_kl_pow_mono_eq0 :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (Heq0 : real_eq (geod_lsum n (fun i : nat =>
                       real_kl_term (r i) (p i) (Hr i) (Hp i))) real_zero)
    (t t1 : nat) (Hle : NatLe t t1),
  real_le_b
    (geod_lsum n (fun i : nat =>
        real_kl_term (r i)
          (geodi_iterate n r Hr eta p Hp Hn t1 i)
          (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t1 i)))
    (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
               (geod_lsum n (fun i : nat =>
                  real_kl_term (r i) (p i) (Hr i) (Hp i)))).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn Heq0 t t1 Hle.
  exact (i4b_policy_iter_kl_pow_mono_B n r Hr eta Heta Hlt1 p Hp
           Hnormr Hnormp Hn
           (i4b_kl0_or_of_eq (geod_lsum n (fun i : nat =>
                real_kl_term (r i) (p i) (Hr i) (Hp i))) Heq0)
           t t1 Hle).
Qed.

(* ============================================================ *)
(* 四、假设审计（全件 Closed，证据在编译日志）                            *)
(* ============================================================ *)

Print Assumptions i4b_kl0_or_of_lt.
Print Assumptions i4b_kl0_or_of_eq.
Print Assumptions i4b_pow_kl_mono_le_b.
Print Assumptions i4b_policy_iter_kl_pow_mono_B.
Print Assumptions i4b_policy_iter_kl_pow_mono_eq0.

(* ============================================================ *)
(* 尾注：诚实登记表                                                        *)
(* 【对接判定】结论 I4 消费位（UpReqGeomIter 尾注）所指缺口「④le_b       *)
(*   乘法保序闭包（非负右因子版）」已由 UpReqPowMonoBridge 件1 落库；     *)

(*   结论 I4 目标形「t ≤ t1 ⟹ KL_{t1} ≤_B κ^t·KL_0」在补充 Or 形证书     *)
(*   Hkl0or 下全闭合——消费位需求满足（草案残差即本证书位）。             *)
(* 【证书位残差｜B⟹Or 单点】Or 形 0 ≤ KL_0 无一般构造性证书：            *)
(*   · 库内已有全为 B 形（geodi_kl_nonneg_B / real_gibbs_inequality_B /  *)
(*     gibbsd_gibbs_inequality），其链根 real_gibbs_core_eps 与          *)

(*     逐 eps 完成不给 Or 分支判定（KL_0>0 与 KL_0==0 构造性不可分，     *)
(*     gibbs 等号条件 r==p 逐点判定同样不可分），B⟹Or 方向显式假设成立，     *)

(*   · 两支可通行支路已登记为接口件（件0a lt 支／件0b eq 支）：消费位    *)
(*     上游能供严格见证或等式见证时任取一支即全闭合（件3 为 eq 支        *)
(*     端到端实例）；                                                    *)
(*   · 有界面 ④件5 亦要求 Or 形 0≤c 前提，同样绕不开本单点——换合成器    *)
(*     变体不消除残差；唯有上游见证，或「sup KL 上界材料＋纯 B 形因子    *)
(*     新合成器」路线（库内上界件显式假设，见 UpReqGeomIter 尾注）。          *)

(*   G3 提取探针 Obj.magic=0（_t20_g3.v，产物目录验后即删）。            *)
(* ============================================================ *)
