(* piu_zz_tau_hb_wave3b.v — KB11 Hb 升格候选子片 3/8（1024 段 Hb0-Hb15·机械升格件·零漂移回读断言已过）。
   [KB12 adaptive resplit] 本件=wave3（1024_0..15 重条区）四等分 b/4；引理自 wave3 逐字搬移，语句/体零改写。
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
(* src piu_zz_tau_enclosure.v L1103-L1123 (assert Hb4) *)
Lemma piu_zz_hb_1024_4 : piu_zz_zprod_seg 1024%nat (512%nat + 1456%nat) 16%nat = ((if zz_in_Pn 1024 1969%nat then Z.of_nat 1969%nat else 1%Z) * ((if zz_in_Pn 1024 1970%nat then Z.of_nat 1970%nat else 1%Z) * ((if zz_in_Pn 1024 1971%nat then Z.of_nat 1971%nat else 1%Z) * ((if zz_in_Pn 1024 1972%nat then Z.of_nat 1972%nat else 1%Z) * ((if zz_in_Pn 1024 1973%nat then Z.of_nat 1973%nat else 1%Z) * ((if zz_in_Pn 1024 1974%nat then Z.of_nat 1974%nat else 1%Z) * ((if zz_in_Pn 1024 1975%nat then Z.of_nat 1975%nat else 1%Z) * ((if zz_in_Pn 1024 1976%nat then Z.of_nat 1976%nat else 1%Z) * ((if zz_in_Pn 1024 1977%nat then Z.of_nat 1977%nat else 1%Z) * ((if zz_in_Pn 1024 1978%nat then Z.of_nat 1978%nat else 1%Z) * ((if zz_in_Pn 1024 1979%nat then Z.of_nat 1979%nat else 1%Z) * ((if zz_in_Pn 1024 1980%nat then Z.of_nat 1980%nat else 1%Z) * ((if zz_in_Pn 1024 1981%nat then Z.of_nat 1981%nat else 1%Z) * ((if zz_in_Pn 1024 1982%nat then Z.of_nat 1982%nat else 1%Z) * ((if zz_in_Pn 1024 1983%nat then Z.of_nat 1983%nat else 1%Z) * (if zz_in_Pn 1024 1984%nat then Z.of_nat 1984%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1984.
    rewrite piu_zz_inPn_1024_1983.
    rewrite piu_zz_inPn_1024_1982.
    rewrite piu_zz_inPn_1024_1981.
    rewrite piu_zz_inPn_1024_1980.
    rewrite piu_zz_inPn_1024_1979.
    rewrite piu_zz_inPn_1024_1978.
    rewrite piu_zz_inPn_1024_1977.
    rewrite piu_zz_inPn_1024_1976.
    rewrite piu_zz_inPn_1024_1975.
    rewrite piu_zz_inPn_1024_1974.
    rewrite piu_zz_inPn_1024_1973.
    rewrite piu_zz_inPn_1024_1972.
    rewrite piu_zz_inPn_1024_1971.
    rewrite piu_zz_inPn_1024_1970.
    rewrite piu_zz_inPn_1024_1969.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1124-L1144 (assert Hb5) *)
Lemma piu_zz_hb_1024_5 : piu_zz_zprod_seg 1024%nat (512%nat + 1440%nat) 16%nat = ((if zz_in_Pn 1024 1953%nat then Z.of_nat 1953%nat else 1%Z) * ((if zz_in_Pn 1024 1954%nat then Z.of_nat 1954%nat else 1%Z) * ((if zz_in_Pn 1024 1955%nat then Z.of_nat 1955%nat else 1%Z) * ((if zz_in_Pn 1024 1956%nat then Z.of_nat 1956%nat else 1%Z) * ((if zz_in_Pn 1024 1957%nat then Z.of_nat 1957%nat else 1%Z) * ((if zz_in_Pn 1024 1958%nat then Z.of_nat 1958%nat else 1%Z) * ((if zz_in_Pn 1024 1959%nat then Z.of_nat 1959%nat else 1%Z) * ((if zz_in_Pn 1024 1960%nat then Z.of_nat 1960%nat else 1%Z) * ((if zz_in_Pn 1024 1961%nat then Z.of_nat 1961%nat else 1%Z) * ((if zz_in_Pn 1024 1962%nat then Z.of_nat 1962%nat else 1%Z) * ((if zz_in_Pn 1024 1963%nat then Z.of_nat 1963%nat else 1%Z) * ((if zz_in_Pn 1024 1964%nat then Z.of_nat 1964%nat else 1%Z) * ((if zz_in_Pn 1024 1965%nat then Z.of_nat 1965%nat else 1%Z) * ((if zz_in_Pn 1024 1966%nat then Z.of_nat 1966%nat else 1%Z) * ((if zz_in_Pn 1024 1967%nat then Z.of_nat 1967%nat else 1%Z) * (if zz_in_Pn 1024 1968%nat then Z.of_nat 1968%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1968.
    rewrite piu_zz_inPn_1024_1967.
    rewrite piu_zz_inPn_1024_1966.
    rewrite piu_zz_inPn_1024_1965.
    rewrite piu_zz_inPn_1024_1964.
    rewrite piu_zz_inPn_1024_1963.
    rewrite piu_zz_inPn_1024_1962.
    rewrite piu_zz_inPn_1024_1961.
    rewrite piu_zz_inPn_1024_1960.
    rewrite piu_zz_inPn_1024_1959.
    rewrite piu_zz_inPn_1024_1958.
    rewrite piu_zz_inPn_1024_1957.
    rewrite piu_zz_inPn_1024_1956.
    rewrite piu_zz_inPn_1024_1955.
    rewrite piu_zz_inPn_1024_1954.
    rewrite piu_zz_inPn_1024_1953.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1145-L1165 (assert Hb6) *)
Lemma piu_zz_hb_1024_6 : piu_zz_zprod_seg 1024%nat (512%nat + 1424%nat) 16%nat = ((if zz_in_Pn 1024 1937%nat then Z.of_nat 1937%nat else 1%Z) * ((if zz_in_Pn 1024 1938%nat then Z.of_nat 1938%nat else 1%Z) * ((if zz_in_Pn 1024 1939%nat then Z.of_nat 1939%nat else 1%Z) * ((if zz_in_Pn 1024 1940%nat then Z.of_nat 1940%nat else 1%Z) * ((if zz_in_Pn 1024 1941%nat then Z.of_nat 1941%nat else 1%Z) * ((if zz_in_Pn 1024 1942%nat then Z.of_nat 1942%nat else 1%Z) * ((if zz_in_Pn 1024 1943%nat then Z.of_nat 1943%nat else 1%Z) * ((if zz_in_Pn 1024 1944%nat then Z.of_nat 1944%nat else 1%Z) * ((if zz_in_Pn 1024 1945%nat then Z.of_nat 1945%nat else 1%Z) * ((if zz_in_Pn 1024 1946%nat then Z.of_nat 1946%nat else 1%Z) * ((if zz_in_Pn 1024 1947%nat then Z.of_nat 1947%nat else 1%Z) * ((if zz_in_Pn 1024 1948%nat then Z.of_nat 1948%nat else 1%Z) * ((if zz_in_Pn 1024 1949%nat then Z.of_nat 1949%nat else 1%Z) * ((if zz_in_Pn 1024 1950%nat then Z.of_nat 1950%nat else 1%Z) * ((if zz_in_Pn 1024 1951%nat then Z.of_nat 1951%nat else 1%Z) * (if zz_in_Pn 1024 1952%nat then Z.of_nat 1952%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1952.
    rewrite piu_zz_inPn_1024_1951.
    rewrite piu_zz_inPn_1024_1950.
    rewrite piu_zz_inPn_1024_1949.
    rewrite piu_zz_inPn_1024_1948.
    rewrite piu_zz_inPn_1024_1947.
    rewrite piu_zz_inPn_1024_1946.
    rewrite piu_zz_inPn_1024_1945.
    rewrite piu_zz_inPn_1024_1944.
    rewrite piu_zz_inPn_1024_1943.
    rewrite piu_zz_inPn_1024_1942.
    rewrite piu_zz_inPn_1024_1941.
    rewrite piu_zz_inPn_1024_1940.
    rewrite piu_zz_inPn_1024_1939.
    rewrite piu_zz_inPn_1024_1938.
    rewrite piu_zz_inPn_1024_1937.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1166-L1186 (assert Hb7) *)
Lemma piu_zz_hb_1024_7 : piu_zz_zprod_seg 1024%nat (512%nat + 1408%nat) 16%nat = ((if zz_in_Pn 1024 1921%nat then Z.of_nat 1921%nat else 1%Z) * ((if zz_in_Pn 1024 1922%nat then Z.of_nat 1922%nat else 1%Z) * ((if zz_in_Pn 1024 1923%nat then Z.of_nat 1923%nat else 1%Z) * ((if zz_in_Pn 1024 1924%nat then Z.of_nat 1924%nat else 1%Z) * ((if zz_in_Pn 1024 1925%nat then Z.of_nat 1925%nat else 1%Z) * ((if zz_in_Pn 1024 1926%nat then Z.of_nat 1926%nat else 1%Z) * ((if zz_in_Pn 1024 1927%nat then Z.of_nat 1927%nat else 1%Z) * ((if zz_in_Pn 1024 1928%nat then Z.of_nat 1928%nat else 1%Z) * ((if zz_in_Pn 1024 1929%nat then Z.of_nat 1929%nat else 1%Z) * ((if zz_in_Pn 1024 1930%nat then Z.of_nat 1930%nat else 1%Z) * ((if zz_in_Pn 1024 1931%nat then Z.of_nat 1931%nat else 1%Z) * ((if zz_in_Pn 1024 1932%nat then Z.of_nat 1932%nat else 1%Z) * ((if zz_in_Pn 1024 1933%nat then Z.of_nat 1933%nat else 1%Z) * ((if zz_in_Pn 1024 1934%nat then Z.of_nat 1934%nat else 1%Z) * ((if zz_in_Pn 1024 1935%nat then Z.of_nat 1935%nat else 1%Z) * (if zz_in_Pn 1024 1936%nat then Z.of_nat 1936%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1936.
    rewrite piu_zz_inPn_1024_1935.
    rewrite piu_zz_inPn_1024_1934.
    rewrite piu_zz_inPn_1024_1933.
    rewrite piu_zz_inPn_1024_1932.
    rewrite piu_zz_inPn_1024_1931.
    rewrite piu_zz_inPn_1024_1930.
    rewrite piu_zz_inPn_1024_1929.
    rewrite piu_zz_inPn_1024_1928.
    rewrite piu_zz_inPn_1024_1927.
    rewrite piu_zz_inPn_1024_1926.
    rewrite piu_zz_inPn_1024_1925.
    rewrite piu_zz_inPn_1024_1924.
    rewrite piu_zz_inPn_1024_1923.
    rewrite piu_zz_inPn_1024_1922.
    rewrite piu_zz_inPn_1024_1921.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.
