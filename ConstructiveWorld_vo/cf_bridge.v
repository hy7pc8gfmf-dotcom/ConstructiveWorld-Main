(* 五字段指针｜使命：B=q_{T−1} 构造面桥＋全谱实例重收——谱理论第二定理：
   对任意周期 T 类（任意部分商列表 l=a_1..a_T），CF 展开的周期块积（列作用规约
   (x,y)↦(A·x+B·y,C·x+D·y)）的 (2,1) 元＝分母流第二分量＝q_{T−1}（首成员分母·
   三路核对独立复算 53/53 零例外的构造性机内化）——块矩阵递推的一般归纳。
   §C CF 构造层：cf1（整周期作用·逐步 (x,y)↦(a·x+y,x)）＋cfqa/cfq（分母流·
     种子 (q_0,q_{−1})=(1,0)）＋cfA/cfB/cfC/cfD（块矩阵四元·基像 (cf1 l 1 0)=
     (cfA,cfC)·(cf1 l 0 1)=(cfB,cfD)）；cf1_lin（线性性＝矩阵幂 Q 层一般归纳
     主件）＋cfA_cons..cfD_cons（块递推：前置 a 时 cfA'=a·cfA+cfB·cfB'=cfA·
     cfC'=a·cfC+cfD·cfD'=cfC）＋cf_det（det＝powneg1 (length l)＝(−1)^T·
     T 奇偶判据面）＋cfC_q（cfC＝q_{T−1}＝cfq 第二分量）＋cf_agree_T1/T2
     （B≡1/B≡a₁ 类级核对——sc_T1/sc_T2 冻结值的构造面重收）。
   §S 桥定理（sc_row2_general 系直用）：cf_bridge_even（T 偶·det=+1 档：
     成员行邻 det≡cfC＝q_{T−1} 常数）／cf_bridge_odd（T 奇·det=−1 档：
     ＝cfC·(−1)^n 交替）——标准种子 (a_0,1)/(1,0)（伴生 G₀=−1）。
   §R 全谱重收层（总表 T≥3 全 27 件＝26 新勘＋D=13 交叉锚·锐度值升序＝CSV 序）：
     每件两发——rec_dD_row2（cf_bridge_even/odd 实例·det 由 cf_det 按 T 奇偶
     自动机内判定）＋rec_dD_den（cfC＝总表 B_rc 数值钉定·vm_compute 可执行面）。
     D=34 单向判据守护：本层 det 全走 cf_det＝powneg1 (length l) 的 T 奇偶形，
     禁 x²≡−1 (mod D) 同余 iff 形。
   §A 审计＋独立复算先行（假件拦截第一道）：整数精确路 ALL PASS 27/27（周期独立
     复算＝CSV 核对｜块积两实现互证｜B 三路核对｜det=(−1)^T｜流恒等式 n≤8｜
     首成员范数 ±1 与 q=B 全核对）＋PA＋Separate Extraction＋vm_compute 数值锚。
   依赖：fib_machine（powneg1/powneg1_S）＋sharp_const（gp/gy/sc_row2_general 系）；
     Stdlib ZArith、List。
   构造性注记：语句面 Z 面等式（sc_row2 同款先例形）＋定义面全透明；零承认、
     零 Abort、零全局假设、零经典逻辑；桥定理（cf1_lin/cf_det/cf_bridge 系）
     结构化收尾零 solver。
   编译配方：rocq c -native-compiler no -q -Q . "" cf_bridge.v *)

Require Import fib_machine.
Require Import sharp_const.
From Stdlib Require Import ZArith.ZArith List.
Import ListNotations.
Open Scope Z_scope.

(* ============================================================ *)
(* §C CF 构造层：整周期作用＋分母流＋块矩阵四元                       *)
(* ============================================================ *)

(* cf1：部分商列表 l=a_1..a_T 的一次整周期作用——逐步 (x,y)↦(a·x+y,x)
   （＝列向量依次过 T(a_1)..T(a_T)，T(a)=(a,1;1,0)） *)
Fixpoint cf1 (l : list Z) (x y : Z) : Z * Z :=
  match l with
  | [] => (x, y)
  | a :: l' => cf1 l' (a * x + y) x
  end.

(* cfqa/cfq：分母流折叠（同序）·种子 (q_0,q_{−1})=(1,0)——步进 (q,q')↦(a·q+q',q) *)
Fixpoint cfqa (l : list Z) (acc : Z * Z) : Z * Z :=
  match l with
  | [] => acc
  | a :: l' => cfqa l' ((a * fst acc + snd acc)%Z, fst acc)
  end.

Definition cfq (l : list Z) : Z * Z := cfqa l (1%Z, 0%Z).

(* 块矩阵四元：基像列 (cf1 l 1 0)=(cfA,cfC)·(cf1 l 0 1)=(cfB,cfD)
   ——cf1 l (x,y)＝M(l)·(x,y)^T·cfC＝M 的 (2,1) 元＝锐度常元位 *)
Definition cfA (l : list Z) : Z := fst (cf1 l 1 0).
Definition cfB (l : list Z) : Z := fst (cf1 l 0 1).
Definition cfC (l : list Z) : Z := snd (cf1 l 1 0).
Definition cfD (l : list Z) : Z := snd (cf1 l 0 1).

Lemma cf1_cons1 : forall (a : Z) (l : list Z) (x y : Z),
  cf1 (a :: l) x y = cf1 l (a * x + y) x.
Proof. intros a l x y. reflexivity. Qed.

(* 线性性＝矩阵幂 Q 层主件：整周期作用由四元决定——cf1 l (x,y)=M(l)·(x,y)^T *)
Theorem cf1_lin : forall (l : list Z) (x y : Z),
  cf1 l x y = ((cfA l * x + cfB l * y)%Z, (cfC l * x + cfD l * y)%Z).
Proof.
  induction l as [|a l IH]; intros x y.
  - unfold cfA, cfB, cfC, cfD. cbn [cf1 fst snd]. f_equal; ring.
  - assert (HA : cfA (a :: l) = (a * cfA l + cfB l)%Z).
    { unfold cfA at 1. rewrite (cf1_cons1 a l 1%Z 0%Z), (IH (a * 1 + 0)%Z 1%Z). cbn [fst]. ring. }
    assert (HB : cfB (a :: l) = cfA l).
    { unfold cfB at 1. rewrite (cf1_cons1 a l 0%Z 1%Z), (IH (a * 0 + 1)%Z 0%Z). cbn [fst]. ring. }
    assert (HC : cfC (a :: l) = (a * cfC l + cfD l)%Z).
    { unfold cfC at 1. rewrite (cf1_cons1 a l 1%Z 0%Z), (IH (a * 1 + 0)%Z 1%Z). cbn [snd]. ring. }
    assert (HD : cfD (a :: l) = cfC l).
    { unfold cfD at 1. rewrite (cf1_cons1 a l 0%Z 1%Z), (IH (a * 0 + 1)%Z 0%Z). cbn [snd]. ring. }
    rewrite (cf1_cons1 a l x y), (IH (a * x + y)%Z x), HA, HB, HC, HD.
    f_equal; ring.
Qed.

(* 块递推四件：前置部分商 a 时 M(a::l)＝M(l)·T(a) 的四元演化 *)
Lemma cfA_cons : forall (a : Z) (l : list Z), cfA (a :: l) = (a * cfA l + cfB l)%Z.
Proof. intros a l. unfold cfA at 1. rewrite (cf1_cons1 a l 1%Z 0%Z), cf1_lin. cbn [fst]. ring. Qed.

Lemma cfB_cons : forall (a : Z) (l : list Z), cfB (a :: l) = cfA l.
Proof. intros a l. unfold cfB at 1. rewrite (cf1_cons1 a l 0%Z 1%Z), cf1_lin. cbn [fst]. ring. Qed.

Lemma cfC_cons : forall (a : Z) (l : list Z), cfC (a :: l) = (a * cfC l + cfD l)%Z.
Proof. intros a l. unfold cfC at 1. rewrite (cf1_cons1 a l 1%Z 0%Z), cf1_lin. cbn [snd]. ring. Qed.

Lemma cfD_cons : forall (a : Z) (l : list Z), cfD (a :: l) = cfC l.
Proof. intros a l. unfold cfD at 1. rewrite (cf1_cons1 a l 0%Z 1%Z), cf1_lin. cbn [snd]. ring. Qed.

(* 行列式＝(−1)^T（det T(a)=−1 沿 T 归纳·T 奇偶判据面） *)
Theorem cf_det : forall l : list Z,
  (cfA l * cfD l - cfB l * cfC l = powneg1 (length l))%Z.
Proof.
  induction l as [|a l IH].
  - unfold cfA, cfB, cfC, cfD. cbn [cf1 fst snd length powneg1]. ring.
  - cbn [length]. rewrite cfA_cons, cfB_cons, cfC_cons, cfD_cons, powneg1_S.
    rewrite <- IH. ring.
Qed.

(* cf1 与分母流折叠互证（同一逐步语义） *)
Lemma cf1_cfqa : forall (l : list Z) (x y : Z), cf1 l x y = cfqa l (x, y).
Proof.
  induction l as [|a l IH]; intros x y.
  - reflexivity.
  - cbn [cf1 cfqa fst snd]. rewrite IH. reflexivity.
Qed.

(* 构造面桥主定理：cfC＝块积 (2,1) 元＝q_{T−1}＝分母流第二分量（首成员分母位） *)
Theorem cfC_q : forall l : list Z, cfC l = snd (cfq l).
Proof. intro l. unfold cfC, cfq. rewrite cf1_cfqa. reflexivity. Qed.

(* 类级核对：T=1 类 B≡1／T=2 类 B≡a₁（sc_T1/sc_T2 冻结值的构造面重收） *)
Lemma cf_agree_T1 : forall a : Z, cfC [a] = 1%Z.
Proof. intro a. unfold cfC. reflexivity. Qed.

Lemma cf_agree_T2 : forall a1 a2 : Z, cfC [a1; a2] = a1.
Proof. intros a1 a2. unfold cfC. cbn [cf1 snd]. ring. Qed.

(* ============================================================ *)
(* §S 桥定理：sc_row2_general 系直用——成员行邻 det 常元＝cfC＝q_{T−1}   *)
(* ============================================================ *)

(* T 偶档（det=+1）：E'_n＝cfC 常数（标准种子 (a_0,1)/(1,0)·G₀=−1） *)
Theorem cf_bridge_even : forall (l : list Z) (x0 : Z) (n : nat),
  (cfA l * cfD l - cfB l * cfC l = 1)%Z ->
  (gy (cfA l) (cfB l) (cfC l) (cfD l) x0 1 n
     * gy (cfA l) (cfB l) (cfC l) (cfD l) 1 0 (S n)
   - gy (cfA l) (cfB l) (cfC l) (cfD l) x0 1 (S n)
     * gy (cfA l) (cfB l) (cfC l) (cfD l) 1 0 n
  = cfC l)%Z.
Proof.
  intros l x0 n Hdet.
  pose proof (sc_row2_general (cfA l) (cfB l) (cfC l) (cfD l) x0 1 1 0 n Hdet) as H.
  rewrite H. ring.
Qed.

(* T 奇档（det=−1）：E'_n＝cfC·(−1)^n 交替 *)
Theorem cf_bridge_odd : forall (l : list Z) (x0 : Z) (n : nat),
  (cfA l * cfD l - cfB l * cfC l = -1)%Z ->
  (gy (cfA l) (cfB l) (cfC l) (cfD l) x0 1 n
     * gy (cfA l) (cfB l) (cfC l) (cfD l) 1 0 (S n)
   - gy (cfA l) (cfB l) (cfC l) (cfD l) x0 1 (S n)
     * gy (cfA l) (cfB l) (cfC l) (cfD l) 1 0 n
  = cfC l * powneg1 n)%Z.
Proof.
  intros l x0 n Hdet.
  pose proof (sc_row2_general_alt (cfA l) (cfB l) (cfC l) (cfD l) x0 1 1 0 n Hdet) as H.
  rewrite H. ring.
Qed.

(* ============================================================ *)
(* §R 全谱重收层：总表 T≥3 全 27 件·锐度值升序＝CSV 序·5 批            *)
(* 每件两发：rec_dD_row2＝cf_bridge_even/odd 实例（det 由 cf_det 按    *)
(* T 奇偶机内判定）＋rec_dD_den＝cfC＝总表 B_rc 数值钉定（可执行面）。  *)
(* D=34 单向判据守护：det 全走 cf_det 的 T 奇偶形，禁同余 iff 形。     *)
(* ============================================================ *)

(* —— D=60（√60=[7;overline{1;2;1;14}]·T=4·even 档）—— *)
Definition l_d60 : list Z := [1;2;1;14].

Lemma rec_d60_row2 : forall n : nat,
  (gy (cfA l_d60) (cfB l_d60) (cfC l_d60) (cfD l_d60) 7 1 n
     * gy (cfA l_d60) (cfB l_d60) (cfC l_d60) (cfD l_d60) 1 0 (S n)
   - gy (cfA l_d60) (cfB l_d60) (cfC l_d60) (cfD l_d60) 7 1 (S n)
     * gy (cfA l_d60) (cfB l_d60) (cfC l_d60) (cfD l_d60) 1 0 n
  = cfC l_d60)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d60 7 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d60_den : (Z.eqb (cfC l_d60) 4) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=59（√59=[7;overline{1;2;7;2;1;14}]·T=6·even 档）—— *)
Definition l_d59 : list Z := [1;2;7;2;1;14].

Lemma rec_d59_row2 : forall n : nat,
  (gy (cfA l_d59) (cfB l_d59) (cfC l_d59) (cfD l_d59) 7 1 n
     * gy (cfA l_d59) (cfB l_d59) (cfC l_d59) (cfD l_d59) 1 0 (S n)
   - gy (cfA l_d59) (cfB l_d59) (cfC l_d59) (cfD l_d59) 7 1 (S n)
     * gy (cfA l_d59) (cfB l_d59) (cfC l_d59) (cfD l_d59) 1 0 n
  = cfC l_d59)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d59 7 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d59_den : (Z.eqb (cfC l_d59) 69) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=58（√58=[7;overline{1;1;1;1;1;1;14}]·T=7·odd 档）—— *)
Definition l_d58 : list Z := [1;1;1;1;1;1;14].

Lemma rec_d58_row2 : forall n : nat,
  (gy (cfA l_d58) (cfB l_d58) (cfC l_d58) (cfD l_d58) 7 1 n
     * gy (cfA l_d58) (cfB l_d58) (cfC l_d58) (cfD l_d58) 1 0 (S n)
   - gy (cfA l_d58) (cfB l_d58) (cfC l_d58) (cfD l_d58) 7 1 (S n)
     * gy (cfA l_d58) (cfB l_d58) (cfC l_d58) (cfD l_d58) 1 0 n
  = cfC l_d58 * powneg1 n)%Z.
Proof.
  intro n. apply (cf_bridge_odd l_d58 7 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d58_den : (Z.eqb (cfC l_d58) 13) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=57（√57=[7;overline{1;1;4;1;1;14}]·T=6·even 档）—— *)
Definition l_d57 : list Z := [1;1;4;1;1;14].

Lemma rec_d57_row2 : forall n : nat,
  (gy (cfA l_d57) (cfB l_d57) (cfC l_d57) (cfD l_d57) 7 1 n
     * gy (cfA l_d57) (cfB l_d57) (cfC l_d57) (cfD l_d57) 1 0 (S n)
   - gy (cfA l_d57) (cfB l_d57) (cfC l_d57) (cfD l_d57) 7 1 (S n)
     * gy (cfA l_d57) (cfB l_d57) (cfC l_d57) (cfD l_d57) 1 0 n
  = cfC l_d57)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d57 7 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d57_den : (Z.eqb (cfC l_d57) 20) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=55（√55=[7;overline{2;2;2;14}]·T=4·even 档）—— *)
Definition l_d55 : list Z := [2;2;2;14].

Lemma rec_d55_row2 : forall n : nat,
  (gy (cfA l_d55) (cfB l_d55) (cfC l_d55) (cfD l_d55) 7 1 n
     * gy (cfA l_d55) (cfB l_d55) (cfC l_d55) (cfD l_d55) 1 0 (S n)
   - gy (cfA l_d55) (cfB l_d55) (cfC l_d55) (cfD l_d55) 7 1 (S n)
     * gy (cfA l_d55) (cfB l_d55) (cfC l_d55) (cfD l_d55) 1 0 n
  = cfC l_d55)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d55 7 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d55_den : (Z.eqb (cfC l_d55) 12) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=54（√54=[7;overline{2;1;6;1;2;14}]·T=6·even 档）—— *)
Definition l_d54 : list Z := [2;1;6;1;2;14].

Lemma rec_d54_row2 : forall n : nat,
  (gy (cfA l_d54) (cfB l_d54) (cfC l_d54) (cfD l_d54) 7 1 n
     * gy (cfA l_d54) (cfB l_d54) (cfC l_d54) (cfD l_d54) 1 0 (S n)
   - gy (cfA l_d54) (cfB l_d54) (cfC l_d54) (cfD l_d54) 7 1 (S n)
     * gy (cfA l_d54) (cfB l_d54) (cfC l_d54) (cfD l_d54) 1 0 n
  = cfC l_d54)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d54 7 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d54_den : (Z.eqb (cfC l_d54) 66) = true.
Proof. vm_compute. reflexivity. Qed.

(* —— D=53（√53=[7;overline{3;1;1;3;14}]·T=5·odd 档）—— *)
Definition l_d53 : list Z := [3;1;1;3;14].

Lemma rec_d53_row2 : forall n : nat,
  (gy (cfA l_d53) (cfB l_d53) (cfC l_d53) (cfD l_d53) 7 1 n
     * gy (cfA l_d53) (cfB l_d53) (cfC l_d53) (cfD l_d53) 1 0 (S n)
   - gy (cfA l_d53) (cfB l_d53) (cfC l_d53) (cfD l_d53) 7 1 (S n)
     * gy (cfA l_d53) (cfB l_d53) (cfC l_d53) (cfD l_d53) 1 0 n
  = cfC l_d53 * powneg1 n)%Z.
Proof.
  intro n. apply (cf_bridge_odd l_d53 7 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d53_den : (Z.eqb (cfC l_d53) 25) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=52（√52=[7;overline{4;1;2;1;4;14}]·T=6·even 档）—— *)
Definition l_d52 : list Z := [4;1;2;1;4;14].

Lemma rec_d52_row2 : forall n : nat,
  (gy (cfA l_d52) (cfB l_d52) (cfC l_d52) (cfD l_d52) 7 1 n
     * gy (cfA l_d52) (cfB l_d52) (cfC l_d52) (cfD l_d52) 1 0 (S n)
   - gy (cfA l_d52) (cfB l_d52) (cfC l_d52) (cfD l_d52) 7 1 (S n)
     * gy (cfA l_d52) (cfB l_d52) (cfC l_d52) (cfD l_d52) 1 0 n
  = cfC l_d52)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d52 7 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d52_den : (Z.eqb (cfC l_d52) 90) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=47（√47=[6;overline{1;5;1;12}]·T=4·even 档）—— *)
Definition l_d47 : list Z := [1;5;1;12].

Lemma rec_d47_row2 : forall n : nat,
  (gy (cfA l_d47) (cfB l_d47) (cfC l_d47) (cfD l_d47) 6 1 n
     * gy (cfA l_d47) (cfB l_d47) (cfC l_d47) (cfD l_d47) 1 0 (S n)
   - gy (cfA l_d47) (cfB l_d47) (cfC l_d47) (cfD l_d47) 6 1 (S n)
     * gy (cfA l_d47) (cfB l_d47) (cfC l_d47) (cfD l_d47) 1 0 n
  = cfC l_d47)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d47 6 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d47_den : (Z.eqb (cfC l_d47) 7) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=46（√46=[6;overline{1;3;1;1;2;6;2;1;1;3;1;12}]·T=12·even 档）—— *)
Definition l_d46 : list Z := [1;3;1;1;2;6;2;1;1;3;1;12].

Lemma rec_d46_row2 : forall n : nat,
  (gy (cfA l_d46) (cfB l_d46) (cfC l_d46) (cfD l_d46) 6 1 n
     * gy (cfA l_d46) (cfB l_d46) (cfC l_d46) (cfD l_d46) 1 0 (S n)
   - gy (cfA l_d46) (cfB l_d46) (cfC l_d46) (cfD l_d46) 6 1 (S n)
     * gy (cfA l_d46) (cfB l_d46) (cfC l_d46) (cfD l_d46) 1 0 n
  = cfC l_d46)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d46 6 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d46_den : (Z.eqb (cfC l_d46) 3588) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=45（√45=[6;overline{1;2;2;2;1;12}]·T=6·even 档）—— *)
Definition l_d45 : list Z := [1;2;2;2;1;12].

Lemma rec_d45_row2 : forall n : nat,
  (gy (cfA l_d45) (cfB l_d45) (cfC l_d45) (cfD l_d45) 6 1 n
     * gy (cfA l_d45) (cfB l_d45) (cfC l_d45) (cfD l_d45) 1 0 (S n)
   - gy (cfA l_d45) (cfB l_d45) (cfC l_d45) (cfD l_d45) 6 1 (S n)
     * gy (cfA l_d45) (cfB l_d45) (cfC l_d45) (cfD l_d45) 1 0 n
  = cfC l_d45)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d45 6 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d45_den : (Z.eqb (cfC l_d45) 24) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=44（√44=[6;overline{1;1;1;2;1;1;1;12}]·T=8·even 档）—— *)
Definition l_d44 : list Z := [1;1;1;2;1;1;1;12].

Lemma rec_d44_row2 : forall n : nat,
  (gy (cfA l_d44) (cfB l_d44) (cfC l_d44) (cfD l_d44) 6 1 n
     * gy (cfA l_d44) (cfB l_d44) (cfC l_d44) (cfD l_d44) 1 0 (S n)
   - gy (cfA l_d44) (cfB l_d44) (cfC l_d44) (cfD l_d44) 6 1 (S n)
     * gy (cfA l_d44) (cfB l_d44) (cfC l_d44) (cfD l_d44) 1 0 n
  = cfC l_d44)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d44 6 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d44_den : (Z.eqb (cfC l_d44) 30) = true.
Proof. vm_compute. reflexivity. Qed.

(* —— D=43（√43=[6;overline{1;1;3;1;5;1;3;1;1;12}]·T=10·even 档）—— *)
Definition l_d43 : list Z := [1;1;3;1;5;1;3;1;1;12].

Lemma rec_d43_row2 : forall n : nat,
  (gy (cfA l_d43) (cfB l_d43) (cfC l_d43) (cfD l_d43) 6 1 n
     * gy (cfA l_d43) (cfB l_d43) (cfC l_d43) (cfD l_d43) 1 0 (S n)
   - gy (cfA l_d43) (cfB l_d43) (cfC l_d43) (cfD l_d43) 6 1 (S n)
     * gy (cfA l_d43) (cfB l_d43) (cfC l_d43) (cfD l_d43) 1 0 n
  = cfC l_d43)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d43 6 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d43_den : (Z.eqb (cfC l_d43) 531) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=41（√41=[6;overline{2;2;12}]·T=3·odd 档）—— *)
Definition l_d41 : list Z := [2;2;12].

Lemma rec_d41_row2 : forall n : nat,
  (gy (cfA l_d41) (cfB l_d41) (cfC l_d41) (cfD l_d41) 6 1 n
     * gy (cfA l_d41) (cfB l_d41) (cfC l_d41) (cfD l_d41) 1 0 (S n)
   - gy (cfA l_d41) (cfB l_d41) (cfC l_d41) (cfD l_d41) 6 1 (S n)
     * gy (cfA l_d41) (cfB l_d41) (cfC l_d41) (cfD l_d41) 1 0 n
  = cfC l_d41 * powneg1 n)%Z.
Proof.
  intro n. apply (cf_bridge_odd l_d41 6 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d41_den : (Z.eqb (cfC l_d41) 5) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=34（√34=[5;overline{1;4;1;10}]·T=4·even 档）—— *)
Definition l_d34 : list Z := [1;4;1;10].

Lemma rec_d34_row2 : forall n : nat,
  (gy (cfA l_d34) (cfB l_d34) (cfC l_d34) (cfD l_d34) 5 1 n
     * gy (cfA l_d34) (cfB l_d34) (cfC l_d34) (cfD l_d34) 1 0 (S n)
   - gy (cfA l_d34) (cfB l_d34) (cfC l_d34) (cfD l_d34) 5 1 (S n)
     * gy (cfA l_d34) (cfB l_d34) (cfC l_d34) (cfD l_d34) 1 0 n
  = cfC l_d34)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d34 5 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d34_den : (Z.eqb (cfC l_d34) 6) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=33（√33=[5;overline{1;2;1;10}]·T=4·even 档）—— *)
Definition l_d33 : list Z := [1;2;1;10].

Lemma rec_d33_row2 : forall n : nat,
  (gy (cfA l_d33) (cfB l_d33) (cfC l_d33) (cfD l_d33) 5 1 n
     * gy (cfA l_d33) (cfB l_d33) (cfC l_d33) (cfD l_d33) 1 0 (S n)
   - gy (cfA l_d33) (cfB l_d33) (cfC l_d33) (cfD l_d33) 5 1 (S n)
     * gy (cfA l_d33) (cfB l_d33) (cfC l_d33) (cfD l_d33) 1 0 n
  = cfC l_d33)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d33 5 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d33_den : (Z.eqb (cfC l_d33) 4) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=32（√32=[5;overline{1;1;1;10}]·T=4·even 档）—— *)
Definition l_d32 : list Z := [1;1;1;10].

Lemma rec_d32_row2 : forall n : nat,
  (gy (cfA l_d32) (cfB l_d32) (cfC l_d32) (cfD l_d32) 5 1 n
     * gy (cfA l_d32) (cfB l_d32) (cfC l_d32) (cfD l_d32) 1 0 (S n)
   - gy (cfA l_d32) (cfB l_d32) (cfC l_d32) (cfD l_d32) 5 1 (S n)
     * gy (cfA l_d32) (cfB l_d32) (cfC l_d32) (cfD l_d32) 1 0 n
  = cfC l_d32)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d32 5 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d32_den : (Z.eqb (cfC l_d32) 3) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=31（√31=[5;overline{1;1;3;5;3;1;1;10}]·T=8·even 档）—— *)
Definition l_d31 : list Z := [1;1;3;5;3;1;1;10].

Lemma rec_d31_row2 : forall n : nat,
  (gy (cfA l_d31) (cfB l_d31) (cfC l_d31) (cfD l_d31) 5 1 n
     * gy (cfA l_d31) (cfB l_d31) (cfC l_d31) (cfD l_d31) 1 0 (S n)
   - gy (cfA l_d31) (cfB l_d31) (cfC l_d31) (cfD l_d31) 5 1 (S n)
     * gy (cfA l_d31) (cfB l_d31) (cfC l_d31) (cfD l_d31) 1 0 n
  = cfC l_d31)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d31 5 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d31_den : (Z.eqb (cfC l_d31) 273) = true.
Proof. vm_compute. reflexivity. Qed.

(* —— D=29（√29=[5;overline{2;1;1;2;10}]·T=5·odd 档）—— *)
Definition l_d29 : list Z := [2;1;1;2;10].

Lemma rec_d29_row2 : forall n : nat,
  (gy (cfA l_d29) (cfB l_d29) (cfC l_d29) (cfD l_d29) 5 1 n
     * gy (cfA l_d29) (cfB l_d29) (cfC l_d29) (cfD l_d29) 1 0 (S n)
   - gy (cfA l_d29) (cfB l_d29) (cfC l_d29) (cfD l_d29) 5 1 (S n)
     * gy (cfA l_d29) (cfB l_d29) (cfC l_d29) (cfD l_d29) 1 0 n
  = cfC l_d29 * powneg1 n)%Z.
Proof.
  intro n. apply (cf_bridge_odd l_d29 5 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d29_den : (Z.eqb (cfC l_d29) 13) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=28（√28=[5;overline{3;2;3;10}]·T=4·even 档）—— *)
Definition l_d28 : list Z := [3;2;3;10].

Lemma rec_d28_row2 : forall n : nat,
  (gy (cfA l_d28) (cfB l_d28) (cfC l_d28) (cfD l_d28) 5 1 n
     * gy (cfA l_d28) (cfB l_d28) (cfC l_d28) (cfD l_d28) 1 0 (S n)
   - gy (cfA l_d28) (cfB l_d28) (cfC l_d28) (cfD l_d28) 5 1 (S n)
     * gy (cfA l_d28) (cfB l_d28) (cfC l_d28) (cfD l_d28) 1 0 n
  = cfC l_d28)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d28 5 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d28_den : (Z.eqb (cfC l_d28) 24) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=23（√23=[4;overline{1;3;1;8}]·T=4·even 档）—— *)
Definition l_d23 : list Z := [1;3;1;8].

Lemma rec_d23_row2 : forall n : nat,
  (gy (cfA l_d23) (cfB l_d23) (cfC l_d23) (cfD l_d23) 4 1 n
     * gy (cfA l_d23) (cfB l_d23) (cfC l_d23) (cfD l_d23) 1 0 (S n)
   - gy (cfA l_d23) (cfB l_d23) (cfC l_d23) (cfD l_d23) 4 1 (S n)
     * gy (cfA l_d23) (cfB l_d23) (cfC l_d23) (cfD l_d23) 1 0 n
  = cfC l_d23)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d23 4 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d23_den : (Z.eqb (cfC l_d23) 5) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=22（√22=[4;overline{1;2;4;2;1;8}]·T=6·even 档）—— *)
Definition l_d22 : list Z := [1;2;4;2;1;8].

Lemma rec_d22_row2 : forall n : nat,
  (gy (cfA l_d22) (cfB l_d22) (cfC l_d22) (cfD l_d22) 4 1 n
     * gy (cfA l_d22) (cfB l_d22) (cfC l_d22) (cfD l_d22) 1 0 (S n)
   - gy (cfA l_d22) (cfB l_d22) (cfC l_d22) (cfD l_d22) 4 1 (S n)
     * gy (cfA l_d22) (cfB l_d22) (cfC l_d22) (cfD l_d22) 1 0 n
  = cfC l_d22)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d22 4 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d22_den : (Z.eqb (cfC l_d22) 42) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=21（√21=[4;overline{1;1;2;1;1;8}]·T=6·even 档）—— *)
Definition l_d21 : list Z := [1;1;2;1;1;8].

Lemma rec_d21_row2 : forall n : nat,
  (gy (cfA l_d21) (cfB l_d21) (cfC l_d21) (cfD l_d21) 4 1 n
     * gy (cfA l_d21) (cfB l_d21) (cfC l_d21) (cfD l_d21) 1 0 (S n)
   - gy (cfA l_d21) (cfB l_d21) (cfC l_d21) (cfD l_d21) 4 1 (S n)
     * gy (cfA l_d21) (cfB l_d21) (cfC l_d21) (cfD l_d21) 1 0 n
  = cfC l_d21)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d21 4 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d21_den : (Z.eqb (cfC l_d21) 12) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=19（√19=[4;overline{2;1;3;1;2;8}]·T=6·even 档）—— *)
Definition l_d19 : list Z := [2;1;3;1;2;8].

Lemma rec_d19_row2 : forall n : nat,
  (gy (cfA l_d19) (cfB l_d19) (cfC l_d19) (cfD l_d19) 4 1 n
     * gy (cfA l_d19) (cfB l_d19) (cfC l_d19) (cfD l_d19) 1 0 (S n)
   - gy (cfA l_d19) (cfB l_d19) (cfC l_d19) (cfD l_d19) 4 1 (S n)
     * gy (cfA l_d19) (cfB l_d19) (cfC l_d19) (cfD l_d19) 1 0 n
  = cfC l_d19)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d19 4 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d19_den : (Z.eqb (cfC l_d19) 39) = true.
Proof. vm_compute. reflexivity. Qed.

(* —— D=14（√14=[3;overline{1;2;1;6}]·T=4·even 档）—— *)
Definition l_d14 : list Z := [1;2;1;6].

Lemma rec_d14_row2 : forall n : nat,
  (gy (cfA l_d14) (cfB l_d14) (cfC l_d14) (cfD l_d14) 3 1 n
     * gy (cfA l_d14) (cfB l_d14) (cfC l_d14) (cfD l_d14) 1 0 (S n)
   - gy (cfA l_d14) (cfB l_d14) (cfC l_d14) (cfD l_d14) 3 1 (S n)
     * gy (cfA l_d14) (cfB l_d14) (cfC l_d14) (cfD l_d14) 1 0 n
  = cfC l_d14)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d14 3 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d14_den : (Z.eqb (cfC l_d14) 4) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=13（√13=[3;overline{1;1;1;1;6}]·T=5·odd 档）—— *)
Definition l_d13 : list Z := [1;1;1;1;6].

Lemma rec_d13_row2 : forall n : nat,
  (gy (cfA l_d13) (cfB l_d13) (cfC l_d13) (cfD l_d13) 3 1 n
     * gy (cfA l_d13) (cfB l_d13) (cfC l_d13) (cfD l_d13) 1 0 (S n)
   - gy (cfA l_d13) (cfB l_d13) (cfC l_d13) (cfD l_d13) 3 1 (S n)
     * gy (cfA l_d13) (cfB l_d13) (cfC l_d13) (cfD l_d13) 1 0 n
  = cfC l_d13 * powneg1 n)%Z.
Proof.
  intro n. apply (cf_bridge_odd l_d13 3 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d13_den : (Z.eqb (cfC l_d13) 5) = true.
Proof. vm_compute. reflexivity. Qed.
(* —— D=7（√7=[2;overline{1;1;1;4}]·T=4·even 档）—— *)
Definition l_d7 : list Z := [1;1;1;4].

Lemma rec_d7_row2 : forall n : nat,
  (gy (cfA l_d7) (cfB l_d7) (cfC l_d7) (cfD l_d7) 2 1 n
     * gy (cfA l_d7) (cfB l_d7) (cfC l_d7) (cfD l_d7) 1 0 (S n)
   - gy (cfA l_d7) (cfB l_d7) (cfC l_d7) (cfD l_d7) 2 1 (S n)
     * gy (cfA l_d7) (cfB l_d7) (cfC l_d7) (cfD l_d7) 1 0 n
  = cfC l_d7)%Z.
Proof.
  intro n. apply (cf_bridge_even l_d7 2 n). rewrite cf_det. reflexivity.
Qed.

Lemma rec_d7_den : (Z.eqb (cfC l_d7) 3) = true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §A 桥审计：数值锚（独立复算逐字核对值）                            *)
(* ============================================================ *)

(* 数值锚一（D=13 块积四元＝FIB5 冻结件 N=[[33,20],[5,3]] 逐字核对） *)
Definition l13s : list Z := [1;1;1;1;6].
Lemma smoke_cf_entries_d13 :
  (cfA l13s, cfB l13s, cfC l13s, cfD l13s) = (33, 20, 5, 3).
Proof. vm_compute. reflexivity. Qed.

(* 数值锚二（D=58·T=7 奇档）：q_{T−1}=13＝总表 B_rc（首成员 99/13 分母位） *)
Definition l58s : list Z := [1;1;1;1;1;1;14].
Lemma smoke_cf_q_d58 : (Z.eqb (snd (cfq l58s)) 13) = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions cf1_lin.
Print Assumptions cfA_cons.
Print Assumptions cfB_cons.
Print Assumptions cfC_cons.
Print Assumptions cfD_cons.
Print Assumptions cf_det.
Print Assumptions cf1_cfqa.
Print Assumptions cfC_q.
Print Assumptions cf_agree_T1.
Print Assumptions cf_agree_T2.
Print Assumptions cf_bridge_even.
Print Assumptions cf_bridge_odd.
Print Assumptions smoke_cf_entries_d13.
Print Assumptions smoke_cf_q_d58.

(* §R 重收件 PA（54 条） *)
Print Assumptions rec_d60_row2.
Print Assumptions rec_d60_den.
Print Assumptions rec_d59_row2.
Print Assumptions rec_d59_den.
Print Assumptions rec_d58_row2.
Print Assumptions rec_d58_den.
Print Assumptions rec_d57_row2.
Print Assumptions rec_d57_den.
Print Assumptions rec_d55_row2.
Print Assumptions rec_d55_den.
Print Assumptions rec_d54_row2.
Print Assumptions rec_d54_den.
Print Assumptions rec_d53_row2.
Print Assumptions rec_d53_den.
Print Assumptions rec_d52_row2.
Print Assumptions rec_d52_den.
Print Assumptions rec_d47_row2.
Print Assumptions rec_d47_den.
Print Assumptions rec_d46_row2.
Print Assumptions rec_d46_den.
Print Assumptions rec_d45_row2.
Print Assumptions rec_d45_den.
Print Assumptions rec_d44_row2.
Print Assumptions rec_d44_den.
Print Assumptions rec_d43_row2.
Print Assumptions rec_d43_den.
Print Assumptions rec_d41_row2.
Print Assumptions rec_d41_den.
Print Assumptions rec_d34_row2.
Print Assumptions rec_d34_den.
Print Assumptions rec_d33_row2.
Print Assumptions rec_d33_den.
Print Assumptions rec_d32_row2.
Print Assumptions rec_d32_den.
Print Assumptions rec_d31_row2.
Print Assumptions rec_d31_den.
Print Assumptions rec_d29_row2.
Print Assumptions rec_d29_den.
Print Assumptions rec_d28_row2.
Print Assumptions rec_d28_den.
Print Assumptions rec_d23_row2.
Print Assumptions rec_d23_den.
Print Assumptions rec_d22_row2.
Print Assumptions rec_d22_den.
Print Assumptions rec_d21_row2.
Print Assumptions rec_d21_den.
Print Assumptions rec_d19_row2.
Print Assumptions rec_d19_den.
Print Assumptions rec_d14_row2.
Print Assumptions rec_d14_den.
Print Assumptions rec_d13_row2.
Print Assumptions rec_d13_den.
Print Assumptions rec_d7_row2.
Print Assumptions rec_d7_den.

From Stdlib Require Import Extraction.
Separate Extraction cf1 cfqa cfq cfA cfB cfC cfD
  smoke_cf_entries_d13 smoke_cf_q_d58
  rec_d60_den rec_d59_den rec_d58_den rec_d57_den rec_d55_den rec_d54_den rec_d53_den
  rec_d52_den rec_d47_den rec_d46_den rec_d45_den rec_d44_den rec_d43_den rec_d41_den
  rec_d34_den rec_d33_den rec_d32_den rec_d31_den rec_d29_den rec_d28_den rec_d23_den
  rec_d22_den rec_d21_den rec_d19_den rec_d14_den rec_d13_den rec_d7_den.
