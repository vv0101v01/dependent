# Module M6：`m6_chu_galois_bridge`（64 位元 Chu 空間對偶、全域伽羅瓦對應、邏輯至核心編譯橋、Morita 等價、局部化分數與博弈語義）

本模組為第二層範疇對偶與跨體系橋接模組，融合 **M1（語法與顯式代換）**、**M2（代數累積宇宙）**、**M3（$\Pi/\Sigma$ 雙向 NbE 核心）** 與 **M4（柯里-霍華德證明與序列演算）**，以硬體 64-bit 位元壓縮實作 **Chu 空間 $\mathrm{Chu}(\mathsf{Set}, \mathbf{2})$** 與 **全域公理——伽羅瓦對應**，並建立雙命名空間至統一伸縮語境之證明編譯器、張量—直和分配同構、Monad 分配律、Morita 等價憑證、右分數局部化屋頂（Localization Roofs）及博弈語義策略隱藏複合。

---

## 一、資料夾內已獲得之公理、定義、命題、引理與定理列表

1. **全域公理 M6.A1（語法—語義伽羅瓦對應與 Chu 自對偶鏡像公理）**：任一 64 位元 Chu 空間 $(A, r : A \times X \to \mathbf{2}, X)$ 誘發反變伽羅瓦伴隨 $s : \mathcal{P}(A) \leftrightarrows \mathcal{P}(X)^{\mathrm{op}} : t$，滿足對任意子集位元遮罩 $S \subseteq A, T \subseteq X$：
   $$T \subseteq s(S) \iff S \subseteq t(T), \qquad (C^\perp)^\perp = C$$
   其形式概念閉包 $(t(s(S)), s(S))$ 滿足嚴格冪等性。
2. **定理 M6.T1（雙命名空間邏輯至統一依賴類型核心函子保持定理）**：M4 分離物件變數與證明變數之構造性證明項 $\Gamma \vdash_{\mathrm{M4}} p : \phi$，經統一索引解算器 `resolve_split_index` 與 `compile_ch_term_to_core` 編譯後，嚴格通過 M3 雙向 NbE 核心類型檢驗 $\llbracket \Gamma \rrbracket \vdash_{\mathrm{M3}} \llbracket p \rrbracket : \llbracket \phi \rrbracket$。
3. **定理 M6.T2（依賴張量—直和分配同構定理）**：對任意依賴謂詞族 $P(x), Q(x)$，`tensor_sum_distribute_forward` 與 `tensor_sum_distribute_backward` 給出機械檢驗通過且滿足 $\beta$-正規往返恆等之同構：
   $$\Sigma(x:D).(P(x) + Q(x)) \;\simeq\; (\Sigma(x:D).P(x)) + (\Sigma(x:D).Q(x))$$
4. **定理 M6.T3（Writer 與 Squash 截斷模態之 Beck Monad 分配律定理）**：`monad_distributive_writer_squash` 構造良類型自然變換 $\lambda_{W,P} : W \times \|P\|_{-1} \to \|W \times P\|_{-1}$，使複合函子 $\mathsf{Squash} \circ \mathsf{Writer}_W$ 構成合法複合單子。
5. **定理 M6.T4（非柯里化 $\Sigma$ 呈現與柯里化 $\Pi$ 呈現之 Morita 等價定理）**：兩種語法呈現之泛中性截面在 M3 NbE 下互逆收斂至定義相等，證明兩理論具等價模型範疇。
6. **定理 M6.T5（可縮擴張局部化右分數演算與博弈策略切消元複合定理）**：局部化屋頂 $A \xleftarrow{\in W} M \xrightarrow{f} B$ 經 Ore 拉回與 $\sigma$-提升複合後，沿可縮截面摺疊與直接函數複合嚴格一致；博弈策略 $A \vdash B$ 與 $B \vdash C$ 經中間競技場隱藏（`compose_game_strategies_hiding`）消去全部內部對話切點（`count_cuts == 0`）。

---

## 二、資料夾內已實作之演算法列表

| 演算法名稱 | 所在檔案 | 時間複雜度 | 功能與硬體/數據結構優化說明 |
| :--- | :--- | :--- | :--- |
| 64-bit 位元矩陣類型與宇宙 Chu 空間建構器 (`build_dtt_chu_space`, `build_universe_chu_space`) | `chu_galois_duality.mbt` | $O(\|A\| \cdot \|X\|)$ 建表；查詢 $O(\|A\|)$ 位元 `AND` | 同步維護行遮罩 `rows` 與轉置列遮罩 `cols`（`UInt64`） |
| 位元級伽羅瓦伴隨、自對偶轉置與概念閉包 (`galois_spec_of`, `galois_models_of`, `verify_galois_adjointness`, `chu_dual`, `concept_closure`) | `chu_galois_duality.mbt` | $O(1)$ 位元包含判定 `(t & ~s(S)) == 0` | 單指令級位元遮罩反轉與交集驗證全域伽羅瓦伴隨律 |
| Chu 態射伴隨恆等檢驗器 (`verify_chu_morphism`) | `chu_galois_duality.mbt` | $O(\|A_1\| \cdot \|X_2\|)$ | 檢驗 $r_2(f_+(a), y) = r_1(a, f_-(y))$ |
| 雙命名空間至統一核心證明編譯器 (`compile_ch_type_to_core`, `compile_ch_term_to_core`) | `chu_galois_duality.mbt` | $O(\|p\| \cdot d)$ | 以布林標記棧精確解算物件／證明變數在統一伸縮語境中之 De Bruijn 索引 |
| 張量—直和分配與 Monad 分配律合成器 (`tensor_sum_distribute_forward/backward`, `monad_distributive_writer_squash`) | `chu_galois_duality.mbt` | $O(\|\phi\|)$ | 合成認證構造性同構項與截斷單子分配項 |
| Morita 等價檢驗、局部化屋頂複合與博弈策略隱藏器 (`verify_curry_morita_equivalence`, `compose_localized_roofs`, `collapse_localized_roof`, `compose_game_strategies_hiding`) | `chu_galois_duality.mbt` | 多項式於項與證明規模 | 結合 M1 $\sigma$-提升、M3 NbE 等價與 M4 切消元隱藏內部通訊 |

---

## 三、資料夾視角的依賴關係圖

```text
  [ dtt/m1_syntax_context ]  [ dtt/m2_universe_cumul ]  [ dtt/m3_pi_sigma_types ]  [ dtt/m4_curry_howard_prop ]
              │                          │                          │                           │
              └──────────────────────────┴────────────┬─────────────┴───────────────────────────┘
                                                      ▼
                                   ┌─────────────────────────────────────┐
                                   │       dtt/m6_chu_galois_bridge      │
                                   │        chu_galois_duality.mbt       │
                                   └──────────────────┬──────────────────┘
                                                      │
                                                      ▼
                                          [ dtt/m7_unified_kernel ]
```

---

## 四、資料夾內動線及接入與輸出接口

### 內部資料動線
1. `build_dtt_chu_space` 與 `build_universe_chu_space` 分別調用 M3 雙向檢驗器與 M2 宇宙蘊涵求解器產生 64-bit `ChuTypingSpace`，提供位元級伽羅瓦伴隨運算。
2. `compile_ch_type_to_core` 與 `compile_ch_term_to_core` 將 M4 邏輯公式與證明項嵌入 M3 核心項並交由 NbE 檢驗。
3. 範疇組合算子分別在 M1（局部化屋頂）、M3（Morita 等價）與 M4（張量—直和分配、Monad 分配律、博弈切消元）上閉環運作。

### 輸出公共接口（Public API）
- **類型與錯誤**：`ChuTypingSpace`, `ChuMorphism`, `LocalizedRoof`, `GameStrategy`, `BridgeError`。
- **Chu 空間與伽羅瓦算子**：`build_dtt_chu_space`, `build_universe_chu_space`, `chu_dual`, `ChuTypingSpace::{galois_spec_of, galois_models_of, verify_galois_adjointness, concept_closure}`, `verify_chu_morphism`。
- **跨模組編譯與範疇算子**：`compile_sort_to_core`, `compile_obj_to_core`, `compile_ch_type_to_core`, `compile_ch_term_to_core`, `tensor_sum_distribute_forward`, `tensor_sum_distribute_backward`, `monad_distributive_writer_squash`, `verify_curry_morita_equivalence`, `compose_localized_roofs`, `collapse_localized_roof`, `compose_game_strategies_hiding`。
