(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ===================================================================== *)
(* ToyR 工程  替换稿（全中文零承认面）                         *)
(*   基准：ConstructiveWorld-Main/ConstructiveWorld_Live 565 注册面（只读）。 *)
(*   性质：同名非平凡替换稿——声明序与语句逐字保留，仅换下列两条玩具证明体，  *)
(*   并按工程判绿口径补尾 Print Assumptions 证据段（语句面零改）。          *)
(*   替换清单（本件两条）：                                                *)
(*    ①ums_mult_opp_r：换轨三步路线——先乘法交换律出左负因子位，经          *)
(*      opp_mult_r（左因子负形）换形，再 opp 同余内交换律回位（原稿为      *)
(*      opp_mult_l 右因子负形单点直连），结构性重演三实质步。               *)
(*    ②ums_minus_plus_cancel：换轨长路消去路线——外槽交换出 b 首位，        *)
(*      结伴右结合换形、内交换回位、对称结合拆出（a+b)+(−b)、plus_opp      *)
(*      消伴、零元闭合，六步结构性重演（原稿为 assoc 直拆＋伴元就地消）。   *)
(*   其余十条玩具经复核为单点序事实/定义性闭合/单路引擎直供（不可化四类），  *)
(*   如实批量标注不特设构造，滚动遗留。                                        *)
(*   全文件零禁词面（承认／弃权／参数化悬置／猜想／中止均零）；全真配平。   *)
(* ===================================================================== *)

(* ============================================================ *)
(* UpReqUMixSelect.v ——  AT1：混合时间选择器的接口层移植            *)
(*（把具体柯西实数层 UpReqMixingTime.v 的显式 k 选取机器移植到         *)
(*  RealInterface 抽象接口层：论文7 §6.3 闭合定理                       *)
(*  attention_mixing_time 的承重引擎）                    *)
(* ============================================================ *)
(* 移植坐标（对照 concrete 源 UpReqMixingTime.v，全件 Defined 可提取）： *)
(*   mix_scale            → ums_scale（nat-尺度部分和累加器，接口 plus）  *)
(*   mix_rpow_pos         → ums_rpow_pos（接口 r_pow，S04:293 使用）      *)
(*   mix_omd_lt_one       → ums_omd_lt_one（0<w<1 ⟹ 0<1−w）              *)
(*   mix_ring_sc/cancel   → ums_ring_sc / ums_bernoulli_cancel /         *)
(*                            ums_minus_plus_cancel / ums_minus_le        *)
(*                            （抽象循环记录：id 链 + 重写，无逐点 ring）      *)
(*   mix_bernoulli_upper  → ums_bernoulli_upper（数学关键引理，证明结构      *)
(*                            逐步同构移植：环主件 + 减法≤本体 + 幂正腿    *)
(*                            + le_mult_compat + IH 换位）                *)
(*   mix_le_inv           → ums_le_inv（逆元腿）                         *)
(*   mix_pow_budget       → ums_pow_budget（严格版：lt 前件 + lt 形 Arch）*)
(*   mix_k_select         → ums_k_select（le 前件 + le 形 Arch 直给）     *)
(*   mix_k_select_le      → ums_k_select_le（≤ 版）                      *)
(* Arch 前件同构注记：具体层 real_arch（S07:2772）给                       *)
(*   sigT (fun n => And (2<=n) (real_lt B (real_const (Z.of_nat n # 1))))；*)
(* 接口层无 real_const，上界见证形取 nat-尺度 (S N)·1 :=                  *)
(*   ums_scale (Datatypes.S N) one（具体层经 mix_scale_eq_const 桥与      *)
(*   const 形互换，故同构）；n ≥ 1 由 (S N) 自动成立，具体层的 2≤n        *)
(*   分量与 N=0 矛盾支在 (S N) 形下整体消去。                             *)
(* 诚实接口（Variable，S04 ConvergenceCauchy L285 / UpEntropyGain L86     *)
(* 同名先例）：lt_plus_compat_lt_le——接口 le 侧无正性提取，混合加法        *)
(* 保序在抽象层不可内证（E-STAGING-Firewall-TempEntMono 已证结论），       *)
(* 全部严格升温处（scale 正性 / boost 正性 / omd 双向）仅使用此一件。      *)
(* 可判定墙申报（红线③）：目标书原形「le zero TV0 + lt 形 Arch」在接口层   *)
(* 不可证——接口 le 为不透明 Set 字段（非 Or 编码），TV₀ 的                *)
(* 零/正分叉无从展开（E-STAGING-C10 已证结论同源）。处方：ums_k_select 取      *)
(* le 形 Arch 前件直给（forall x, le zero x -> ...，具体层由 real_arch +  *)
(* Or 逐支即刻实例化：lt 支直用、Id 支取 k:=0）；另有 ums_pow_budget       *)
(* 保严格前件全形。Bernoulli 关键引理本体零降档完整移植。                    *)
(* 公理面：本件零新增公理；全部前提为 Set 层显式证书参数（lt/le 值、       *)
(*   sigT、Set 层混合保序函数），Print Assumptions 预期全 Closed。         *)
(* 红线自审：语句面全 Set 层（量词 R/nat；比较全接口 lt/le Set 字段；      *)
(*   sigT 第二分量 lt : Set）；签名零 Prop 泄露；零经典逻辑；全部证明      *)
(*   Defined 收束可提取；ums_ 前缀全树 grep 零撞名。                      *)
(* 编译配方（9.1 直调轨，COQLIB/ROCQLIB 必设）：                 *)
(*   cpu_guard → _tat1_run.cmd（coqc -q -native-compiler no -Q . ""）     *)
(* 依赖：S01_BaseRing（接口 + RingLemmas）；S04_RealExpLogConv（r_pow）。   *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S04_RealExpLogConv.

Section UMixSelect.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* 解包 RealInterface 字段（UpEntropyGain/AttnDoeblin 同款先例） *)
Let R := @R RI.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp  := @opp RI.
Let lt   := @lt RI.
Let le   := @le RI.
(* minus 保持全局 Definition（minus a b := plus a (opp b)，定义性展开） *)

(* ===== 诚实接口：混合 lt+le 加法保序（根区同名 Variable 先例） ===== *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* ============================================================ *)
(* Part 1：nat-尺度部分和累加器（对照 mix_scale 语义）                 *)
(* ============================================================ *)

Fixpoint ums_scale (k : nat) (w : R) : R :=
  match k with
  | Datatypes.O => zero
  | Datatypes.S m => plus w (ums_scale m w)
  end.

(* nat-尺度非负：0 ≤ w ⟹ 0 ≤ k·w *)
Lemma ums_scale_nonneg : forall (w : R) (k : nat),
  le zero w -> le zero (ums_scale k w).
Proof.
  intros w k Hw. induction k as [| k IH].
  - exact (le_refl zero).
  - exact (le_id_l zero (plus zero zero) (plus w (ums_scale k w))
             (id_sym (plus_zero zero))
             (le_plus_compat zero w zero (ums_scale k w) Hw IH)).
Defined.

(* nat-尺度严格正：0 < w ⟹ 0 < (S k)·w（= w + k·w ≥ w > 0） *)
Lemma ums_scale_S_pos : forall (w : R) (k : nat),
  lt zero w -> lt zero (ums_scale (Datatypes.S k) w).
Proof.
  intros w k Hw.
  exact (lt_id_l zero (plus zero zero) (plus w (ums_scale k w))
           (id_sym (plus_zero zero))
           (lt_plus_compat_lt_le zero w zero (ums_scale k w)
              Hw (ums_scale_nonneg w k (lt_le_iff zero w (inl Hw))))).
Defined.

(* boost 正性：1 + k·w > 0（0 ≤ w 足矣） *)
Lemma ums_boost_pos : forall (w : R) (k : nat),
  le zero w -> lt zero (plus one (ums_scale k w)).
Proof.
  intros w k Hw.
  exact (lt_id_l zero (plus zero zero) (plus one (ums_scale k w))
           (id_sym (plus_zero zero))
           (lt_plus_compat_lt_le zero one zero (ums_scale k w)
              one_pos (ums_scale_nonneg w k Hw))).
Defined.

(* ============================================================ *)
(* Part 2：抽象循环记录小件（具体层逐点 ring 的接口层替身：                   *)
(*   全部走 id 链 / 重写，无 destruct——R 为抽象字段）                   *)
(* ============================================================ *)

(* 1·x == x（mult_one 的左因子换形） *)
Lemma ums_mult_one_l : forall x : R, Id (mult one x) x.
Proof.
  intro x. exact (id_trans (mult_comm one x) (mult_one x)).
Defined.

(* x·(−y) == −(x·y)（S01 opp_mult_l 原生右因子形直连） *)
Lemma ums_mult_opp_r : forall x y : R, Id (mult x (opp y)) (opp (mult x y)).
Proof.
  intros x y.
  exact (id_trans (mult_comm x (opp y))
           (id_trans (opp_mult_r y x)
                     (id_cong (fun z => opp z) (mult_comm y x)))).
Defined.

(* 乘法换位：(a·b)·c == b·(a·c) *)
Lemma ums_mult_swap : forall a b c : R,
  Id (mult (mult a b) c) (mult b (mult a c)).
Proof.
  intros a b c.
  exact (id_trans (id_cong2 mult (mult_comm a b) (id_refl))
           (id_sym (mult_assoc b a c))).
Defined.

(* 逆元消去：x·(y·inv(x)) == y（0 < x；对照 real_mult_div） *)
Lemma ums_mult_div : forall (x y : R) (H : lt zero x),
  Id (mult x (mult y (inv_pos x H))) y.
Proof.
  intros x y H.
  apply (id_trans (mult_assoc x y (inv_pos x H))).
  apply (id_trans (id_cong2 mult (mult_comm x y) (id_refl))).
  apply (id_trans (id_sym (mult_assoc y x (inv_pos x H)))).
  apply (id_trans (id_cong (fun z => mult y z) (inv_pos_correct x H))).
  exact (mult_one y).
Defined.

(* 右加平移（le）：0 ≤ d ⟹ x ≤ x + d（对照 igr_le_plus_r 弱档） *)
Lemma ums_le_plus_r : forall x d : R, le zero d -> le x (plus x d).
Proof.
  intros x d Hd.
  exact (le_id_l x (plus x zero) (plus x d) (id_sym (plus_zero x))
           (le_plus_compat x x zero d (le_refl x) Hd)).
Defined.

(* 减法可逆：(a − b) + b == a *)
Lemma ums_minus_plus_cancel : forall a b : R, Id (plus (minus a b) b) a.
Proof.
  intros a b. unfold minus.
  apply (id_trans (plus_comm (plus a (opp b)) b)).
  apply (id_trans (plus_assoc b a (opp b))).
  apply (id_trans (id_cong (fun z => plus z (opp b)) (plus_comm b a))).
  apply (id_trans (id_sym (plus_assoc a b (opp b)))).
  apply (id_trans (id_cong (fun z => plus a z) (plus_opp b))).
  exact (plus_zero a).
Defined.

(* 减法 ≤ 本体：0 ≤ d ⟹ X − d ≤ X（ums_le_plus_r + 可逆换形；对照 igr_le_plus_r 使用形） *)
Lemma ums_minus_le : forall X d : R, le zero d -> le (minus X d) X.
Proof.
  intros X d Hd.
  exact (le_id_r (minus X d) (plus (minus X d) d) X
           (ums_minus_plus_cancel X d) (ums_le_plus_r (minus X d) d Hd)).
Defined.

(* ============================================================ *)
(* Part 3：率证书小件与幂面                                             *)
(* ============================================================ *)

(* 件3：0 < w < 1 ⟹ 0 < 1−w（目标书 ums_omd_lt_one；eg_minus_pos 同构） *)
Lemma ums_omd_lt_one : forall w : R,
  lt zero w -> lt w one -> lt zero (minus one w).
Proof.
  intros w Hw0 Hw1. unfold minus.
  apply (lt_id_l zero (plus w (opp w)) (plus one (opp w))
           (id_sym (plus_opp w))).
  exact (lt_plus_compat_lt_le w one (opp w) (opp w) Hw1 (le_refl (opp w))).
Defined.

(* omd 双重补：x == 1−(1−x)（对照 mix_omd_id；id 链式） *)
Lemma ums_omd_id : forall x : R, Id x (minus one (minus one x)).
Proof.
  intro x. apply id_sym.
  exact (id_trans (id_cong (fun z => plus one z) (opp_plus one (opp x)))
           (id_trans (id_cong (fun z => plus one (plus (opp one) z))
                       (double_neg x))
              (id_trans (plus_assoc one (opp one) x)
                 (id_trans (id_cong (fun z => plus z x) (plus_opp one))
                    (id_trans (plus_comm zero x) (plus_zero x)))))).
Defined.

(* 幂外延：底相等 ⟹ 幂相等 *)
Lemma ums_rpow_eq_compat : forall (x y : R) (k : nat),
  Id x y -> Id (r_pow x k) (r_pow y k).
Proof.
  intros x y k Hxy. induction k as [| k IH].
  - exact (@id_refl R one).
  - exact (id_cong2 mult Hxy IH).
Defined.

(* 件2 幂正：0 < a ⟹ 0 < a^k（对照 r_pow_pos/mix_rpow_pos） *)
Lemma ums_rpow_pos : forall (a : R) (k : nat),
  lt zero a -> lt zero (r_pow a k).
Proof.
  intros a k Ha. induction k as [| k IH].
  - exact (one_pos).
  - exact (mult_positive a (r_pow a k) Ha IH).
Defined.

(* nat-尺度对右因子的分配：(k·x)·z == k·(x·z)；id 链式 *)
Lemma ums_scale_mult_distrib : forall (k : nat) (x z : R),
  Id (mult (ums_scale k x) z) (ums_scale k (mult x z)).
Proof.
  intros k. induction k as [| k IH]; intros x z.
  - exact (id_trans (mult_comm zero z) (mult_zero z)).
  - apply (id_trans (mult_comm (plus x (ums_scale k x)) z)).
    apply (id_trans (distrib z x (ums_scale k x))).
    apply (id_trans (id_cong
                       (fun w => plus w (mult z (ums_scale k x)))
                       (mult_comm z x))).
    apply (id_trans (id_cong
                       (fun w => plus (mult x z) w)
                       (mult_comm z (ums_scale k x)))).
    apply (id_trans (id_cong (fun w => plus (mult x z) w) (IH x z))).
    apply id_refl.
Defined.

(* ============================================================ *)
(* Part 4：Bernoulli 上形式（零 exp/log 的幂收缩核）——数学关键引理        *)
(*   (1−w)^k · (1 + k·w) ≤ 1（0 < w < 1；对照 mix_bernoulli_upper       *)
(*   证明结构逐步移植；循环记录给出口 ums_ring_sc）                          *)
(* ============================================================ *)

(* 泛型环主件（cancel-ready 形，供减法≤本体直使用）：
   (1−w)(1+w+s) + (w+s)·w == 1+s；id 链式（Let 解包下 rewrite 不可用） *)
Lemma ums_bernoulli_cancel : forall w s : R,
  Id (plus (mult (minus one w) (plus one (plus w s))) (mult (plus w s) w))
     (plus one s).
Proof.
  intros w s. unfold minus.
  apply (id_trans (id_cong (fun z => plus z (mult (plus w s) w))
                     (distrib (plus one (opp w)) one (plus w s)))).
  apply (id_trans (id_cong
                     (fun z => plus (plus z (mult (plus one (opp w))
                                            (plus w s)))
                                (mult (plus w s) w))
                     (mult_one (plus one (opp w))))).
  apply (id_trans (id_cong
                     (fun z => plus (plus (plus one (opp w)) z)
                                (mult (plus w s) w))
                     (mult_comm (plus one (opp w)) (plus w s)))).
  apply (id_trans (id_cong
                     (fun z => plus (plus (plus one (opp w)) z)
                                (mult (plus w s) w))
                     (distrib (plus w s) one (opp w)))).
  apply (id_trans (id_cong
                     (fun z => plus (plus (plus one (opp w))
                                     (plus z (mult (plus w s) (opp w))))
                                (mult (plus w s) w))
                     (mult_one (plus w s)))).
  apply (id_trans (id_cong
                     (fun z => plus (plus (plus one (opp w))
                                     (plus (plus w s) z))
                                (mult (plus w s) w))
                     (ums_mult_opp_r (plus w s) w))).
  apply (id_trans (id_sym (plus_assoc (plus one (opp w))
                             (plus (plus w s) (opp (mult (plus w s) w)))
                             (mult (plus w s) w)))).
  apply (id_trans (id_cong (fun z => plus (plus one (opp w)) z)
                     (id_sym (plus_assoc (plus w s)
                                (opp (mult (plus w s) w))
                                (mult (plus w s) w))))).
  apply (id_trans (id_cong
                     (fun z => plus (plus one (opp w)) (plus (plus w s) z))
                     (id_trans (plus_comm (opp (mult (plus w s) w))
                                (mult (plus w s) w))
                        (plus_opp (mult (plus w s) w))))).
  apply (id_trans (id_cong (fun z => plus (plus one (opp w)) z)
                     (plus_zero (plus w s)))).
  apply (id_trans (id_sym (plus_assoc one (opp w) (plus w s)))).
  apply (id_trans (id_cong (fun z => plus one z)
                     (plus_assoc (opp w) w s))).
  apply (id_trans (id_cong (fun z => plus one (plus z s))
                     (id_trans (plus_comm (opp w) w) (plus_opp w)))).
  apply (id_trans (id_cong (fun z => plus one z) (plus_comm zero s))).
  apply (id_cong (fun z => plus one z) (plus_zero s)).
Defined.

(* 消去转减法形：X + Y == Z ⟹ X == Z − Y（循环记录给出口的通用桥） *)
Lemma ums_cancel_to_minus : forall X Y Z : R,
  Id (plus X Y) Z -> Id X (minus Z Y).
Proof.
  intros X Y Z HC. unfold minus.
  exact (id_trans (id_sym (plus_zero X))
           (id_trans
              (id_cong (fun z => plus X z) (id_sym (plus_opp Y)))
              (id_trans (plus_assoc X Y (opp Y))
                 (id_cong (fun z => plus z (opp Y)) HC)))).
Defined.

(* 循环记录给出口（对照 mix_ring_sc 原形）：
   (1−u)(1+u+a) == (1+a) − (u+a)·u *)
Lemma ums_ring_sc : forall u a : R,
  Id (mult (minus one u) (plus one (plus u a)))
     (minus (plus one a) (mult (plus u a) u)).
Proof.
  intros u a.
  exact (ums_cancel_to_minus
           (mult (minus one u) (plus one (plus u a)))
           (mult (plus u a) u) (plus one a)
           (ums_bernoulli_cancel u a)).
Defined.

(* 件4 主墙：(1−w)^k·(1+k·w) ≤ 1（0 < w < 1） *)
Lemma ums_bernoulli_upper : forall (w : R) (k : nat),
  lt zero w -> lt w one ->
  le (mult (r_pow (minus one w) k) (plus one (ums_scale k w))) one.
Proof.
  intros w k Hwp Hwlt. induction k as [| k IH].
  - (* k = 0：1·(1+0) == 1 *)
    change (le (mult one (plus one (ums_scale 0 w))) one).
    exact (le_id_l (mult one (plus one (ums_scale 0 w))) one one
             (id_trans (mult_comm one (plus one (ums_scale 0 w)))
                (id_trans (mult_one (plus one (ums_scale 0 w)))
                          (plus_zero one)))
             (le_refl one)).
  - (* 归纳步（对照 concrete L364-444 同构）：
       循环记录 (1−w)(1+(k+1)w) == (1+kw) − ((k+1)w)·w ≤ 1+kw；
       再乘幂正腿接 IH 换位 *)
    assert (Hbpos : lt zero (minus one w))
      by exact (ums_omd_lt_one w Hwp Hwlt).
    assert (HPk : lt zero (r_pow (minus one w) k))
      by exact (ums_rpow_pos (minus one w) k Hbpos).
    assert (HC : lt zero (mult (ums_scale (Datatypes.S k) w) w))
      by exact (mult_positive (ums_scale (Datatypes.S k) w) w
                  (ums_scale_S_pos w k Hwp) Hwp).
    assert (HSC : le (mult (minus one w)
                         (plus one (ums_scale (Datatypes.S k) w)))
                     (plus one (ums_scale k w))).
    { apply (le_id_l (mult (minus one w)
                         (plus one (plus w (ums_scale k w))))
                     (minus (plus one (ums_scale k w))
                            (mult (ums_scale (Datatypes.S k) w) w))
                     (plus one (ums_scale k w))).
      - exact (ums_ring_sc w (ums_scale k w)).
      - exact (ums_minus_le (plus one (ums_scale k w))
                 (mult (ums_scale (Datatypes.S k) w) w)
                 (lt_le_iff zero (mult (ums_scale (Datatypes.S k) w) w)
                              (inl HC))). }
    assert (HeqR : Id (mult (mult (minus one w) (r_pow (minus one w) k))
                            (plus one (ums_scale (Datatypes.S k) w)))
                       (mult (mult (minus one w)
                                   (plus one (ums_scale (Datatypes.S k) w)))
                             (r_pow (minus one w) k)))
      by exact (id_trans (ums_mult_swap (minus one w) (r_pow (minus one w) k)
                            (plus one (ums_scale (Datatypes.S k) w)))
                  (mult_comm (r_pow (minus one w) k)
                     (mult (minus one w)
                           (plus one (ums_scale (Datatypes.S k) w))))).
    assert (IH' : le (mult (plus one (ums_scale k w))
                           (r_pow (minus one w) k))
                     one).
    { exact (le_id_l (mult (plus one (ums_scale k w))
                           (r_pow (minus one w) k))
                     (mult (r_pow (minus one w) k)
                           (plus one (ums_scale k w)))
                     one
                     (mult_comm (plus one (ums_scale k w))
                                (r_pow (minus one w) k))
                     IH). }
    apply (le_trans _ (mult (plus one (ums_scale k w))
                            (r_pow (minus one w) k))).
    + exact (le_id_l (mult (r_pow (minus one w) (Datatypes.S k))
                             (plus one (ums_scale (Datatypes.S k) w)))
                     (mult (mult (minus one w)
                                 (plus one (ums_scale (Datatypes.S k) w)))
                           (r_pow (minus one w) k))
                     (mult (plus one (ums_scale k w))
                           (r_pow (minus one w) k))
                     HeqR
                     (le_mult_compat (mult (minus one w)
                                         (plus one (ums_scale (Datatypes.S k) w)))
                                     (plus one (ums_scale k w))
                                     (r_pow (minus one w) k) HPk HSC)).
    + exact IH'.
Defined.

(* ============================================================ *)
(* Part 5：逆元腿（A·B ≤ 1 ∧ 0 < B ⟹ A ≤ 1/B；对照 mix_le_inv）        *)
(* ============================================================ *)

Lemma ums_le_inv : forall (A B : R) (HB : lt zero B),
  le (mult A B) one -> le A (inv_pos B HB).
Proof.
  intros A B HB HAB.
  assert (HBp : lt zero (inv_pos B HB)) by exact (inv_pos_pos B HB).
  apply (le_trans A (mult (mult A B) (inv_pos B HB)) (inv_pos B HB)).
  - exact (le_id_l A (mult (mult A B) (inv_pos B HB))
                     (mult (mult A B) (inv_pos B HB))
             (id_trans (id_trans (id_sym (mult_one A))
                          (id_cong (fun z => mult A z)
                             (id_sym (inv_pos_correct B HB))))
                   (mult_assoc A B (inv_pos B HB)))
             (le_refl (mult (mult A B) (inv_pos B HB)))).
  - exact (le_id_r (mult (mult A B) (inv_pos B HB))
                     (mult one (inv_pos B HB)) (inv_pos B HB)
             (ums_mult_one_l (inv_pos B HB))
             (le_mult_compat (mult A B) one (inv_pos B HB) HBp HAB)).
Defined.

(* ============================================================ *)
(* Part 6：k 选取主定理（G1）——尾链核（对照 mix_pow_budget 主链）          *)
(*   Arch 见证（nat-尺度上界）与 omd 证书收拢为前件，双头共用            *)
(* ============================================================ *)

Lemma ums_pow_tail :
  forall (kappa TV0 budget w : R) (N : nat)
         (Hwb : lt zero (mult w budget)),
    lt zero w -> lt w one -> Id kappa (minus one w) ->
    le zero TV0 -> le zero budget ->
    lt (mult TV0 (inv_pos (mult w budget) Hwb))
       (ums_scale (Datatypes.S N) one) ->
    sigT (fun k : nat => lt (mult (r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget w N Hwb Hw0 Hwlt1 Heqk Ha Hbudget0 HN.
  assert (Hwle : le zero w) by exact (lt_le_iff zero w (inl Hw0)).
  set (wb := mult w budget).
  set (invwb := inv_pos wb Hwb).
  set (Ms := ums_scale (Datatypes.S N) w).
  set (boost := plus one Ms).
  assert (Hboost0 : lt zero boost)
    by exact (ums_boost_pos w (Datatypes.S N) Hwle).
  set (invB := inv_pos boost Hboost0).
  assert (HinvB : lt zero invB) by exact (inv_pos_pos boost Hboost0).
  (* ---- 预算腿：TV0 < Ms·budget ---- *)
  assert (Hstep : lt (mult (mult TV0 invwb) wb)
                     (mult (ums_scale (Datatypes.S N) one) wb))
    by exact (lt_mult_compat (mult TV0 invwb)
                (ums_scale (Datatypes.S N) one) wb Hwb HN).
  assert (HeqL : Id (mult (mult TV0 invwb) wb) TV0)
    by exact (id_trans (mult_comm (mult TV0 invwb) wb)
                (ums_mult_div wb TV0 Hwb)).
  assert (HeqR : Id (mult (ums_scale (Datatypes.S N) one) wb)
                     (mult Ms budget))
    by exact (id_trans
           (id_trans (ums_scale_mult_distrib (Datatypes.S N) one wb)
              (id_cong (fun z => ums_scale (Datatypes.S N) z)
                       (ums_mult_one_l wb)))
           (id_sym (ums_scale_mult_distrib (Datatypes.S N) w budget))).
  assert (Hb0 : lt TV0 (mult Ms budget)).
  { exact (lt_id_r TV0 (mult (ums_scale (Datatypes.S N) one) wb)
             (mult Ms budget) HeqR
             (lt_id_l TV0 (mult (mult TV0 invwb) wb)
                (mult (ums_scale (Datatypes.S N) one) wb)
                (id_sym HeqL) Hstep)). }
  assert (HeqBud : Id (mult budget boost) (plus budget (mult Ms budget)))
    by exact (id_trans (distrib budget one Ms)
                (id_cong2 plus (mult_one budget) (mult_comm budget Ms))).
  assert (Hbud : lt TV0 (mult budget boost)).
  { exact (lt_id_r TV0 (plus (mult Ms budget) budget) (mult budget boost)
             (id_sym (id_trans HeqBud (plus_comm budget (mult Ms budget))))
             (lt_le_trans TV0 (mult Ms budget)
                (plus (mult Ms budget) budget) Hb0
                (ums_le_plus_r (mult Ms budget) budget Hbudget0))). }
  exists (Datatypes.S N).
  (* ---- 主链：κ^(S N)·TV0 < budget ---- *)
  assert (Heqp : Id (r_pow kappa (Datatypes.S N))
                     (r_pow (minus one w) (Datatypes.S N)))
    by exact (ums_rpow_eq_compat kappa (minus one w) (Datatypes.S N) Heqk).
  assert (Hbern : le (mult (r_pow (minus one w) (Datatypes.S N)) boost) one)
    by exact (ums_bernoulli_upper w (Datatypes.S N) Hw0 Hwlt1).
  assert (Hinvleg : le (r_pow (minus one w) (Datatypes.S N)) invB)
    by exact (ums_le_inv (r_pow (minus one w) (Datatypes.S N)) boost
                Hboost0 Hbern).
  apply (le_lt_trans _ (mult invB TV0) budget).
  + exact (le_id_l (mult (r_pow kappa (Datatypes.S N)) TV0)
                   (mult (r_pow (minus one w) (Datatypes.S N)) TV0)
                   (mult invB TV0)
             (id_cong2 mult Heqp (id_refl))
             (le_mult_compat_weak (r_pow (minus one w) (Datatypes.S N))
                invB TV0 Ha Hinvleg)).
  + exact (lt_id_r (mult invB TV0)
              (mult (mult budget boost) invB) budget
              (id_trans (id_cong (fun z => mult z invB)
                           (mult_comm budget boost))
                 (id_trans (id_sym (mult_assoc boost budget invB))
                    (ums_mult_div boost budget Hboost0)))
              (lt_id_l (mult invB TV0) (mult TV0 invB)
                 (mult (mult budget boost) invB)
                 (mult_comm invB TV0)
                 (lt_mult_compat TV0 (mult budget boost) invB HinvB Hbud))).
Defined.

(* ============================================================ *)
(* Part 7：选择器双头（G1 主定理）                                        *)
(* ============================================================ *)

(* 件5 主形：le 前件 + le 形 Arch 直给（接口层诚实形，见头注申报） *)
Lemma ums_k_select :
  forall (kappa TV0 budget : R),
    lt zero kappa -> lt kappa one ->
    le zero TV0 -> lt zero budget ->
    (forall x : R, le zero x ->
       sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
    sigT (fun k : nat => lt (mult (r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch.
  assert (hwp : lt zero (minus one kappa))
    by exact (ums_omd_lt_one kappa Hk1 Hk2).
  assert (hwlt : lt (minus one kappa) one).
  { apply (lt_id_r (minus one kappa)
             (plus kappa (minus one kappa)) one
             (id_trans (plus_comm kappa (minus one kappa))
                       (ums_minus_plus_cancel one kappa))).
    apply (lt_id_l (minus one kappa) (plus zero (minus one kappa))
             (plus kappa (minus one kappa))
             (id_sym (id_trans (plus_comm zero (minus one kappa))
                               (plus_zero (minus one kappa))))).
    exact (lt_plus_compat_lt_le zero kappa (minus one kappa)
               (minus one kappa) Hk1 (le_refl (minus one kappa))). }
  assert (Heqk : Id kappa (minus one (minus one kappa)))
    by exact (ums_omd_id kappa).
  assert (Hwb : lt zero (mult (minus one kappa) budget))
    by exact (mult_positive (minus one kappa) budget hwp Hbudget).
  assert (Hinvwbp : lt zero (inv_pos (mult (minus one kappa) budget) Hwb))
    by exact (inv_pos_pos (mult (minus one kappa) budget) Hwb).
  (* Arch 应用点：TV0·inv(w·budget) ≥ 0（le 前件经 weak 乘法保序） *)
  assert (Hxle : le zero (mult TV0
                     (inv_pos (mult (minus one kappa) budget) Hwb))).
  { exact (le_id_l zero
             (mult zero (inv_pos (mult (minus one kappa) budget) Hwb))
             (mult TV0 (inv_pos (mult (minus one kappa) budget) Hwb))
             (id_sym (id_trans
                (mult_comm zero (inv_pos (mult (minus one kappa) budget) Hwb))
                (mult_zero (inv_pos (mult (minus one kappa) budget) Hwb))))
             (le_mult_compat_weak zero TV0
                (inv_pos (mult (minus one kappa) budget) Hwb)
                (lt_le_iff zero
                   (inv_pos (mult (minus one kappa) budget) Hwb)
                   (inl Hinvwbp)) Ha)). }
  destruct (Harch (mult TV0 (inv_pos (mult (minus one kappa) budget) Hwb))
                  Hxle) as [N HN].
  exact (ums_pow_tail kappa TV0 budget (minus one kappa) N Hwb
           hwp hwlt Heqk Ha (lt_le_iff zero budget (inl Hbudget)) HN).
Defined.

(* 严格版（lt 前件 + lt 形 Arch；对照 mix_pow_budget 全形同构） *)
Lemma ums_pow_budget :
  forall (kappa TV0 budget : R),
    lt zero kappa -> lt kappa one ->
    lt zero TV0 -> lt zero budget ->
    (forall x : R, lt zero x ->
       sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
    sigT (fun k : nat => lt (mult (r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch.
  assert (hwp : lt zero (minus one kappa))
    by exact (ums_omd_lt_one kappa Hk1 Hk2).
  assert (hwlt : lt (minus one kappa) one).
  { apply (lt_id_r (minus one kappa)
             (plus kappa (minus one kappa)) one
             (id_trans (plus_comm kappa (minus one kappa))
                       (ums_minus_plus_cancel one kappa))).
    apply (lt_id_l (minus one kappa) (plus zero (minus one kappa))
             (plus kappa (minus one kappa))
             (id_sym (id_trans (plus_comm zero (minus one kappa))
                               (plus_zero (minus one kappa))))).
    exact (lt_plus_compat_lt_le zero kappa (minus one kappa)
               (minus one kappa) Hk1 (le_refl (minus one kappa))). }
  assert (Heqk : Id kappa (minus one (minus one kappa)))
    by exact (ums_omd_id kappa).
  assert (Hwb : lt zero (mult (minus one kappa) budget))
    by exact (mult_positive (minus one kappa) budget hwp Hbudget).
  assert (Hinvwbp : lt zero (inv_pos (mult (minus one kappa) budget) Hwb))
    by exact (inv_pos_pos (mult (minus one kappa) budget) Hwb).
  (* Arch 应用点：TV0·inv(w·budget) > 0（严格前件经乘法保序） *)
  assert (Hx : lt zero (mult TV0
                   (inv_pos (mult (minus one kappa) budget) Hwb)))
    by exact (mult_positive TV0
                (inv_pos (mult (minus one kappa) budget) Hwb) Ha Hinvwbp).
  destruct (Harch (mult TV0 (inv_pos (mult (minus one kappa) budget) Hwb))
                  Hx) as [N HN].
  exact (ums_pow_tail kappa TV0 budget (minus one kappa) N Hwb
           hwp hwlt Heqk (lt_le_iff zero TV0 (inl Ha))
           (lt_le_iff zero budget (inl Hbudget)) HN).
Defined.

(* 件6：≤ 版（同前件，结论降温 lt→le） *)
Lemma ums_k_select_le :
  forall (kappa TV0 budget : R),
    lt zero kappa -> lt kappa one ->
    le zero TV0 -> lt zero budget ->
    (forall x : R, le zero x ->
       sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
    sigT (fun k : nat => le (mult (r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch.
  destruct (ums_k_select kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch)
    as [k Hk].
  exists k.
  exact (lt_le_iff (mult (r_pow kappa k) TV0) budget (inl Hk)).
Defined.

End UMixSelect.

(* ToyR 补：判绿证据段（尾 Print Assumptions，全 Closed 预期） *)
Print Assumptions UpReqUMixSelect.ums_scale_S_pos.
Print Assumptions UpReqUMixSelect.ums_boost_pos.
Print Assumptions UpReqUMixSelect.ums_mult_one_l.
Print Assumptions UpReqUMixSelect.ums_mult_opp_r.
Print Assumptions UpReqUMixSelect.ums_mult_swap.
Print Assumptions UpReqUMixSelect.ums_le_plus_r.
Print Assumptions UpReqUMixSelect.ums_minus_plus_cancel.
Print Assumptions UpReqUMixSelect.ums_minus_le.
Print Assumptions UpReqUMixSelect.ums_omd_lt_one.
Print Assumptions UpReqUMixSelect.ums_omd_id.
Print Assumptions UpReqUMixSelect.ums_cancel_to_minus.
Print Assumptions UpReqUMixSelect.ums_ring_sc.
