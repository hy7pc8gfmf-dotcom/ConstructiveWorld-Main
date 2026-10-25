(* piu_zz_tau_hb_wave3a.v — KB11 Hb 升格候选子片 3/8（1024 段 Hb0-Hb15·机械升格件·零漂移回读断言已过）。
   [KB12 adaptive resplit] 本件=wave3（1024_0..15 重条区）四等分 a/4；引理自 wave3 逐字搬移，语句/体零改写。
   使命：consumer 片 assert (HbN : <封闭语句>) + brace 块逐块升格为独立引理（语句/证明体逐字保留，
         抽取器对每生成件回读 diff 断言通过），使 128 小件可全并行独立编译（各自独立进程内存清零），
         替代 20h 单体磨；本件为候选稿，落地须过试炮与终门，不替代正本。
   依赖：piu_zz_tau_enclosure_bank4（Require Export 链末前件，传递覆盖 bank1..bank3 与 base）、
         piu_zz_poincare_engine、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   对标：piu_zz_tau_enclosure.v（3275 行 post-fix·原巨件 md5 494c8738 分段账）zzPhi_512 段 L103-L774 /
         zzPhi_1024 段 L1019-L3034 的 assert (HbN) 块逐字升格。
   构造性：本片语句零假设、零公理；语句全封闭（右边=bank 事实闭式积），
         证明体只吃 bank 引理＋cbn＋reflexivity；块间零依赖边（ledger 实测）。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_hb_wave3.v *)
Require Export piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
(* src piu_zz_tau_enclosure.v L1019-L1039 (assert Hb0) *)
Lemma piu_zz_hb_1024_0 : piu_zz_zprod_seg 1024%nat (512%nat + 1520%nat) 16%nat = ((if zz_in_Pn 1024 2033%nat then Z.of_nat 2033%nat else 1%Z) * ((if zz_in_Pn 1024 2034%nat then Z.of_nat 2034%nat else 1%Z) * ((if zz_in_Pn 1024 2035%nat then Z.of_nat 2035%nat else 1%Z) * ((if zz_in_Pn 1024 2036%nat then Z.of_nat 2036%nat else 1%Z) * ((if zz_in_Pn 1024 2037%nat then Z.of_nat 2037%nat else 1%Z) * ((if zz_in_Pn 1024 2038%nat then Z.of_nat 2038%nat else 1%Z) * ((if zz_in_Pn 1024 2039%nat then Z.of_nat 2039%nat else 1%Z) * ((if zz_in_Pn 1024 2040%nat then Z.of_nat 2040%nat else 1%Z) * ((if zz_in_Pn 1024 2041%nat then Z.of_nat 2041%nat else 1%Z) * ((if zz_in_Pn 1024 2042%nat then Z.of_nat 2042%nat else 1%Z) * ((if zz_in_Pn 1024 2043%nat then Z.of_nat 2043%nat else 1%Z) * ((if zz_in_Pn 1024 2044%nat then Z.of_nat 2044%nat else 1%Z) * ((if zz_in_Pn 1024 2045%nat then Z.of_nat 2045%nat else 1%Z) * ((if zz_in_Pn 1024 2046%nat then Z.of_nat 2046%nat else 1%Z) * ((if zz_in_Pn 1024 2047%nat then Z.of_nat 2047%nat else 1%Z) * (if zz_in_Pn 1024 2048%nat then Z.of_nat 2048%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_2048.
    rewrite piu_zz_inPn_1024_2047.
    rewrite piu_zz_inPn_1024_2046.
    rewrite piu_zz_inPn_1024_2045.
    rewrite piu_zz_inPn_1024_2044.
    rewrite piu_zz_inPn_1024_2043.
    rewrite piu_zz_inPn_1024_2042.
    rewrite piu_zz_inPn_1024_2041.
    rewrite piu_zz_inPn_1024_2040.
    rewrite piu_zz_inPn_1024_2039.
    rewrite piu_zz_inPn_1024_2038.
    rewrite piu_zz_inPn_1024_2037.
    rewrite piu_zz_inPn_1024_2036.
    rewrite piu_zz_inPn_1024_2035.
    rewrite piu_zz_inPn_1024_2034.
    rewrite piu_zz_inPn_1024_2033.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1040-L1060 (assert Hb1) *)
Lemma piu_zz_hb_1024_1 : piu_zz_zprod_seg 1024%nat (512%nat + 1504%nat) 16%nat = ((if zz_in_Pn 1024 2017%nat then Z.of_nat 2017%nat else 1%Z) * ((if zz_in_Pn 1024 2018%nat then Z.of_nat 2018%nat else 1%Z) * ((if zz_in_Pn 1024 2019%nat then Z.of_nat 2019%nat else 1%Z) * ((if zz_in_Pn 1024 2020%nat then Z.of_nat 2020%nat else 1%Z) * ((if zz_in_Pn 1024 2021%nat then Z.of_nat 2021%nat else 1%Z) * ((if zz_in_Pn 1024 2022%nat then Z.of_nat 2022%nat else 1%Z) * ((if zz_in_Pn 1024 2023%nat then Z.of_nat 2023%nat else 1%Z) * ((if zz_in_Pn 1024 2024%nat then Z.of_nat 2024%nat else 1%Z) * ((if zz_in_Pn 1024 2025%nat then Z.of_nat 2025%nat else 1%Z) * ((if zz_in_Pn 1024 2026%nat then Z.of_nat 2026%nat else 1%Z) * ((if zz_in_Pn 1024 2027%nat then Z.of_nat 2027%nat else 1%Z) * ((if zz_in_Pn 1024 2028%nat then Z.of_nat 2028%nat else 1%Z) * ((if zz_in_Pn 1024 2029%nat then Z.of_nat 2029%nat else 1%Z) * ((if zz_in_Pn 1024 2030%nat then Z.of_nat 2030%nat else 1%Z) * ((if zz_in_Pn 1024 2031%nat then Z.of_nat 2031%nat else 1%Z) * (if zz_in_Pn 1024 2032%nat then Z.of_nat 2032%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_2032.
    rewrite piu_zz_inPn_1024_2031.
    rewrite piu_zz_inPn_1024_2030.
    rewrite piu_zz_inPn_1024_2029.
    rewrite piu_zz_inPn_1024_2028.
    rewrite piu_zz_inPn_1024_2027.
    rewrite piu_zz_inPn_1024_2026.
    rewrite piu_zz_inPn_1024_2025.
    rewrite piu_zz_inPn_1024_2024.
    rewrite piu_zz_inPn_1024_2023.
    rewrite piu_zz_inPn_1024_2022.
    rewrite piu_zz_inPn_1024_2021.
    rewrite piu_zz_inPn_1024_2020.
    rewrite piu_zz_inPn_1024_2019.
    rewrite piu_zz_inPn_1024_2018.
    rewrite piu_zz_inPn_1024_2017.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1061-L1081 (assert Hb2) *)
Lemma piu_zz_hb_1024_2 : piu_zz_zprod_seg 1024%nat (512%nat + 1488%nat) 16%nat = ((if zz_in_Pn 1024 2001%nat then Z.of_nat 2001%nat else 1%Z) * ((if zz_in_Pn 1024 2002%nat then Z.of_nat 2002%nat else 1%Z) * ((if zz_in_Pn 1024 2003%nat then Z.of_nat 2003%nat else 1%Z) * ((if zz_in_Pn 1024 2004%nat then Z.of_nat 2004%nat else 1%Z) * ((if zz_in_Pn 1024 2005%nat then Z.of_nat 2005%nat else 1%Z) * ((if zz_in_Pn 1024 2006%nat then Z.of_nat 2006%nat else 1%Z) * ((if zz_in_Pn 1024 2007%nat then Z.of_nat 2007%nat else 1%Z) * ((if zz_in_Pn 1024 2008%nat then Z.of_nat 2008%nat else 1%Z) * ((if zz_in_Pn 1024 2009%nat then Z.of_nat 2009%nat else 1%Z) * ((if zz_in_Pn 1024 2010%nat then Z.of_nat 2010%nat else 1%Z) * ((if zz_in_Pn 1024 2011%nat then Z.of_nat 2011%nat else 1%Z) * ((if zz_in_Pn 1024 2012%nat then Z.of_nat 2012%nat else 1%Z) * ((if zz_in_Pn 1024 2013%nat then Z.of_nat 2013%nat else 1%Z) * ((if zz_in_Pn 1024 2014%nat then Z.of_nat 2014%nat else 1%Z) * ((if zz_in_Pn 1024 2015%nat then Z.of_nat 2015%nat else 1%Z) * (if zz_in_Pn 1024 2016%nat then Z.of_nat 2016%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_2016.
    rewrite piu_zz_inPn_1024_2015.
    rewrite piu_zz_inPn_1024_2014.
    rewrite piu_zz_inPn_1024_2013.
    rewrite piu_zz_inPn_1024_2012.
    rewrite piu_zz_inPn_1024_2011.
    rewrite piu_zz_inPn_1024_2010.
    rewrite piu_zz_inPn_1024_2009.
    rewrite piu_zz_inPn_1024_2008.
    rewrite piu_zz_inPn_1024_2007.
    rewrite piu_zz_inPn_1024_2006.
    rewrite piu_zz_inPn_1024_2005.
    rewrite piu_zz_inPn_1024_2004.
    rewrite piu_zz_inPn_1024_2003.
    rewrite piu_zz_inPn_1024_2002.
    rewrite piu_zz_inPn_1024_2001.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1082-L1102 (assert Hb3) *)
Lemma piu_zz_hb_1024_3 : piu_zz_zprod_seg 1024%nat (512%nat + 1472%nat) 16%nat = ((if zz_in_Pn 1024 1985%nat then Z.of_nat 1985%nat else 1%Z) * ((if zz_in_Pn 1024 1986%nat then Z.of_nat 1986%nat else 1%Z) * ((if zz_in_Pn 1024 1987%nat then Z.of_nat 1987%nat else 1%Z) * ((if zz_in_Pn 1024 1988%nat then Z.of_nat 1988%nat else 1%Z) * ((if zz_in_Pn 1024 1989%nat then Z.of_nat 1989%nat else 1%Z) * ((if zz_in_Pn 1024 1990%nat then Z.of_nat 1990%nat else 1%Z) * ((if zz_in_Pn 1024 1991%nat then Z.of_nat 1991%nat else 1%Z) * ((if zz_in_Pn 1024 1992%nat then Z.of_nat 1992%nat else 1%Z) * ((if zz_in_Pn 1024 1993%nat then Z.of_nat 1993%nat else 1%Z) * ((if zz_in_Pn 1024 1994%nat then Z.of_nat 1994%nat else 1%Z) * ((if zz_in_Pn 1024 1995%nat then Z.of_nat 1995%nat else 1%Z) * ((if zz_in_Pn 1024 1996%nat then Z.of_nat 1996%nat else 1%Z) * ((if zz_in_Pn 1024 1997%nat then Z.of_nat 1997%nat else 1%Z) * ((if zz_in_Pn 1024 1998%nat then Z.of_nat 1998%nat else 1%Z) * ((if zz_in_Pn 1024 1999%nat then Z.of_nat 1999%nat else 1%Z) * (if zz_in_Pn 1024 2000%nat then Z.of_nat 2000%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_2000.
    rewrite piu_zz_inPn_1024_1999.
    rewrite piu_zz_inPn_1024_1998.
    rewrite piu_zz_inPn_1024_1997.
    rewrite piu_zz_inPn_1024_1996.
    rewrite piu_zz_inPn_1024_1995.
    rewrite piu_zz_inPn_1024_1994.
    rewrite piu_zz_inPn_1024_1993.
    rewrite piu_zz_inPn_1024_1992.
    rewrite piu_zz_inPn_1024_1991.
    rewrite piu_zz_inPn_1024_1990.
    rewrite piu_zz_inPn_1024_1989.
    rewrite piu_zz_inPn_1024_1988.
    rewrite piu_zz_inPn_1024_1987.
    rewrite piu_zz_inPn_1024_1986.
    rewrite piu_zz_inPn_1024_1985.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.
