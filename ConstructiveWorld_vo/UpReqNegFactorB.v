(* ============================================================ *)
(* ToyR 玩具证替换件 —— T269 台账席 战役包AD（tier2 末批二）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   t27_le_nonpos_to_nonneg_opp（原 L71，2 句玩具证）                    *)
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
(* UpReqNegFactorB.v *)
(* *)
(* 目的： le_b 乘法保序的负右因子反变面补全。 *)
(* 主件： t27_le_b_mult_r_nonpos_opp / t27_le_b_mult_r_negstrict 反变定律族。 *)
(* 依赖： CW_ConstructiveWorld_219、UpRealLeB、UpRealLeB3、UpReqPowMonoBridge。 *)
(* 备注： 承幂单调桥件头注的诚实边界注记；非正因子情形为显式补全腿。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqNegFactorB.v —— le_b 乘法保序·负右因子反变面补全（席 T27）        *)
(*   任务书源＝席 X3d 结果件 UpReqPowMonoBridge.v 头注诚实边界注记：      *)
(*   「负右因子反变面未落（邻接缺口，套路已在卡）」——即 c ≤ 0 时乘法     *)
(*   反变：x ≤_B y 给 y·c ≤_B x·c（负因子翻转不等方向）。本件补全该面，   *)
(*   与正面件1（x3d_le_b_mult_r_nonneg_or：0≤c 给 a·c ≤_B b·c 保序）     *)
(*   配对成 Or 形因子证书强度下的完整乘法保序两面家族。                  *)
(* ---------------------------------------------------------------- *)
(* 构造路线（取负共轭，eps 证人翻转零手工重排）：                          *)
(*   b·c ≤_B a·c ⟺ −(a·c) ≤_B −(b·c)（le_b 取负反序，UpRealLeB3 件5      *)
(*   leb3_le_b_opp_rev——其证内 d>0 见证下 x<y+d ⟺ −y+d<−x，恰是「eps    *)
(*   挂位随符号翻转」的定理化，d 在两侧成对消去）⟸ a·(−c) ≤_B b·(−c)     *)
(*   （＝正面件1 于因子 d:=−c 处直用，d ≥ 0 证书在位）＋ real_opp_mult /  *)
(*   real_opp_opp / real_eq_mult_compat 双端等式运输。                   *)
(*   因子正性证书形态：正面取 0≤c（Or 形），负面取 0≤−c（Or 形，与正面   *)
(*   逐槽对位）；c ≤ 0 证书经件0 桥（real_opp_le_compat + real_opp_zero  *)
(*   换形）入共轭核。                                                    *)
(* 五件清单：                                                            *)
(*   件0 t27_le_nonpos_to_nonneg_opp：c ≤ 0 给 0 ≤ −c（Or 形证书换形桥；  *)
(*      正面 x3d 件4 桥的负号镜像）；                                    *)
(*   件1 t27_le_b_mult_r_nonpos_opp：共轭核——0 ≤ −c（Or 形）给           *)
(*      b·c ≤_B a·c（反变面主合成器，正面件1 的取负共轭）；              *)
(*   件2 t27_le_b_mult_r_nonpos_or：任务书逐字语句——x ≤_B y、c ≤ 0 给    *)
(*      y·c ≤_B x·c（件0 桥一接入件1）；                                 *)
(*   件3 t27_le_b_mult_l_nonpos_or：左因子反变形 c·y ≤_B c·x（comm 双运输，*)
(*      正面 x3d 件2 的负号镜像）；                                      *)
(*   件4 t27_le_b_mult_r_negstrict：严格负因子对照形 c < 0 给 y·c ≤_B    *)
(*      x·c（lt 转 Or 后一跳件2；正面 x3d 件3 严格对照形的负号镜像）。    *)
(* 对称面锚（完整乘法保序家族，Or 形因子证书强度，两面对合）：             *)
(*   正面 UpReqPowMonoBridge.v 件1 x3d_le_b_mult_r_nonneg_or：           *)
(*      a ≤_B b ∧ 0≤c 给 a·c ≤_B b·c（保序）；                           *)

(*      a ≤_B b ∧ c≤0 给 b·c ≤_B a·c（反变）。                           *)
(*   两面在 c==0 处退化一致（y·0 == x·0，mult_zero 完成由正面件1 的       *)

(* 诚实登记表：因子仅 B 形已知（real_le_b c real_zero，无 Or 形证书）的     *)
(*   负面版仍显式假设——卡点与正面件4 尾注同款，即 B⟹Or 转换位（构造性不可   *)
(*   通，c 的符号二分无证人）；禁硬凑（分层保底纪律）。                   *)
(* ---------------------------------------------------------------- *)
(* 红线自检：零未闭合证明（全 Qed）；零新依赖面（仅 Require 既有绿库，    *)
(*   含今日新绿 UpReqPowMonoBridge.vo 只读消费）；语句面全 Set 值         *)
(*   （real_le_b/real_le/real_lt 全 Set，Or 为库内 A+B 形）；纯 term-mode *)
(*   组装（real_eq 非 Id 禁改写，全链 real_eq_trans/运输族）；禁词全零    *)
(*   （按全文件计含头注）。                                              *)
(* 编译配方（消费式，vo 树前置；引号从略防注释串警告）：                  *)

(*   ConstructiveWorld_vo EMPTY -Q . EMPTY UpReqNegFactorB.v             *)
(*   （EMPTY 处实为空串实参；cpu_guard 包装零裸调，CoreN 2；              *)
(*     先 -vos 秒审再全量。）                                            *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB3.
Require Import UpReqPowMonoBridge.

(* ============================================================ *)
(* 〇、负因子证书桥：c ≤ 0（Or 形）给 0 ≤ −c（Or 形）                     *)
(*   取负反序（real_opp_le_compat）＋ 负零归一（real_opp_zero）换形。      *)
(*   正面 x3d 件4（Or 给 B 单向桥）的负号镜像面。                         *)
(* ============================================================ *)
Lemma t27_le_nonpos_to_nonneg_opp : forall c : Real,
  real_le c real_zero -> real_le real_zero (real_opp c).
Proof.
  intros c Hc.
  exact (RealSetoid.real_le_id_l real_zero (real_opp real_zero)           (real_opp c)           (real_eq_sym (real_opp real_zero) real_zero real_opp_zero)           (real_opp_le_compat c real_zero Hc)).
Qed.

(* ============================================================ *)
(* 一、共轭核：0 ≤ −c（Or 形）给 b·c ≤_B a·c                              *)
(*   链：正面件1 于因子 −c 处（Hrev）→ le_b 取负反序（Hflip，eps 翻转     *)
(*   步由 leb3_le_b_opp_rev 承接）→ real_opp_mult＋opp 对合 双端等式      *)
(*   运输（HoppA/HoppB）→ eq_r／eq_l 双运输完成。                         *)
(* ============================================================ *)
Lemma t27_le_b_mult_r_nonpos_opp : forall a b c : Real,
  real_le_b a b -> real_le real_zero (real_opp c) ->
  real_le_b (real_mult b c) (real_mult a c).
Proof.
  intros a b c H Hc0.
  (* 正面保序于负因子共轭位：a·(−c) ≤_B b·(−c) *)
  assert (Hrev : real_le_b (real_mult a (real_opp c))
                           (real_mult b (real_opp c)))
    by exact (x3d_le_b_mult_r_nonneg_or a b (real_opp c) H Hc0).
  (* le_b 取负反序：−(b·(−c)) ≤_B −(a·(−c)) *)
  assert (Hflip : real_le_b
                    (real_opp (real_mult b (real_opp c)))
                    (real_opp (real_mult a (real_opp c))))
    by exact (leb3_le_b_opp_rev (real_mult a (real_opp c))
                                (real_mult b (real_opp c)) Hrev).
  (* 右端换形：−(a·(−c)) == a·c（opp 入乘＋对合归一） *)
  assert (HoppA : real_eq (real_opp (real_mult a (real_opp c)))
                          (real_mult a c)).
  { apply (real_eq_trans _ (real_mult a (real_opp (real_opp c))) _).
    - exact (real_opp_mult a (real_opp c)).
    - apply (RealSetoid.real_eq_mult_compat a
               (real_opp (real_opp c)) a c).
      + apply real_eq_refl.
      + exact (real_opp_opp c). }
  (* 左端换形：−(b·(−c)) == b·c（同款） *)
  assert (HoppB : real_eq (real_opp (real_mult b (real_opp c)))
                          (real_mult b c)).
  { apply (real_eq_trans _ (real_mult b (real_opp (real_opp c))) _).
    - exact (real_opp_mult b (real_opp c)).
    - apply (RealSetoid.real_eq_mult_compat b
               (real_opp (real_opp c)) b c).
      + apply real_eq_refl.
      + exact (real_opp_opp c). }
  (* eq_l／eq_r 双运输完成：b·c ≤_B a·c *)
  exact (leb3_le_b_eq_r (real_mult b c)
           (real_opp (real_mult a (real_opp c))) (real_mult a c)
           (leb3_le_b_eq_l (real_opp (real_mult b (real_opp c)))
              (real_mult b c)
              (real_opp (real_mult a (real_opp c))) HoppB Hflip)
           HoppA).
Qed.

(* ============================================================ *)
(* 二、主件：任务书逐字语句——x ≤_B y 且 c ≤ 0 给 y·c ≤_B x·c              *)
(*   件0 桥一接入共轭核。与正面件1（x3d_le_b_mult_r_nonneg_or）           *)
(*   逐槽对位：证书 0≤c 换 c≤0，结论方向翻转。                            *)
(* ============================================================ *)
Lemma t27_le_b_mult_r_nonpos_or : forall a b c : Real,
  real_le_b a b -> real_le c real_zero ->
  real_le_b (real_mult b c) (real_mult a c).
Proof.
  intros a b c H Hc.
  apply t27_le_b_mult_r_nonpos_opp.
  - exact H.
  - exact (t27_le_nonpos_to_nonneg_opp c Hc).
Qed.

(* ============================================================ *)
(* 三、左因子反变形：c·y ≤_B c·x（comm 双运输平移件2）                     *)
(*   正面 x3d 件2 的负号镜像。                                           *)
(* ============================================================ *)
Lemma t27_le_b_mult_l_nonpos_or : forall a b c : Real,
  real_le_b a b -> real_le c real_zero ->
  real_le_b (real_mult c b) (real_mult c a).
Proof.
  intros a b c H Hc.
  apply (leb3_le_b_eq_l (real_mult b c) (real_mult c b) (real_mult c a)).
  - apply real_mult_comm.
  - apply (leb3_le_b_eq_r (real_mult b c) (real_mult a c) (real_mult c a)).
    + exact (t27_le_b_mult_r_nonpos_or a b c H Hc).
    + apply real_mult_comm.
Qed.

(* ============================================================ *)
(* 四、严格负因子对照形：c < 0 给 y·c ≤_B x·c                             *)
(*   lt 转 Or（real_lt_le_iff_req 取 inl 支）后一跳件2。                  *)
(*   正面 x3d 件3（严格正因子对照形）的负号镜像。                         *)
(* ============================================================ *)
Lemma t27_le_b_mult_r_negstrict : forall a b c : Real,
  real_le_b a b -> real_lt c real_zero ->
  real_le_b (real_mult b c) (real_mult a c).
Proof.
  intros a b c H Hc.
  apply t27_le_b_mult_r_nonpos_or.
  - exact H.
  - exact (RealSetoid.real_lt_le_iff_req c real_zero (inl Hc)).
Qed.

(* ============================================================ *)
(* 五、假设审计（全件证据在编译日志）                                     *)
(* ============================================================ *)

Print Assumptions t27_le_nonpos_to_nonneg_opp.
Print Assumptions t27_le_b_mult_r_nonpos_opp.
Print Assumptions t27_le_b_mult_r_nonpos_or.
Print Assumptions t27_le_b_mult_l_nonpos_or.
Print Assumptions t27_le_b_mult_r_negstrict.

(* ============================================================ *)
(* 尾注：诚实登记表                                                        *)
(* 【对称面结果】负面反变面（件2 主件）与正面保序面（x3d 件1）合成        *)
(*   Or 形因子证书强度下的完整乘法保序两面对：符号证书在手时，乘法        *)
(*   保序／反变方向由因子符号唯一确定，两面经取负共轭互为镜像。           *)
(* 【显式假设对位】因子仅 B 形已知（无 Or 形符号证书）的负面版＝正面件4       *)
(*   尾注显式假设的镜像，卡点同为 B⟹Or 转换位；两面显式假设形状对称，禁硬凑。     *)
(* ============================================================ *)
