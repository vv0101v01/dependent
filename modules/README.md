# `modules/`（依賴類型論十四大模組群總覽：涵蓋附件一與附件二全部十九大概念）

本資料夾承載依賴類型論兩階段共十四個 MoonBit 模組，嚴格遵循「先建立零跨模組耦合之獨立基礎模組，再透過範疇極限、Kan 擴張、Grothendieck 纖維化、Chu 空間對偶、局部化、推出融合與半直積組合成上層橋接與大一統核心」之工程架構：

- **第一階段獨立基礎模組（`m1..m4`）**：類型、項、判斷、上下文、$\Pi$-類型、$\Sigma$-類型、代數宇宙、無煩擾累積宇宙、柯里-霍華德對應、命題即類型。
- **第一階段範疇融合核心（`m5..m7`）**：Grothendieck 纖維化與 Kan 擴張、64-bit Chu 空間與全域伽羅瓦對應、半直積與伸縮短正合序列統一核心。
- **第二階段獨立基礎模組（`m8..m11`）**：嚴格正歸納類型、歸納-遞歸類型（IR）、歸納-歸納類型（II）、共同代數與無窮流、仿射與量化類型（QTT）、依賴多型性、隱含參數重寫與模式合一、型別強制轉換、結構型別與名義型別。
- **第二階段範疇對偶與全棧總成核心（`m12..m14`）**：始代數—終共同代數 Chu 對偶與雙模擬局部化、零開銷隱含至量化精化橋與結構紀錄推出融合、十九概念全棧總成系統。

---

## 一、資料夾內已獲得之定理列表（跨十四子模組匯總）

1. **M1–M4 第一階段基礎定理群**：64-bit 位元摘要與嚴格化顯式 $\sigma$-代換交換定理；Fuss-Free 累積宇宙編解碼 $\beta/\eta$-單射定理、伽羅瓦正權環反駁完備性定理與 Ramsey-Dilworth 宇宙分層定理；Kripke NbE $\beta\eta$-決定性、依賴柯里化與 Skolem 選擇同構定理；Gentzen 序列切消元與自然演繹正規化交換圖定理、CPS 古典嵌入與認證證明抹除提取定理。
2. **M5–M7 第一階段範疇融合定理群**：劈裂笛卡兒重索引函子性、左右 Kan 擴張（$\Sigma_\pi \dashv \pi^* \dashv \Pi_\pi$）與 Beck-Chevalley 自然同構定理、層截面黏合定理；64-bit Chu 空間自對偶鏡像與全域伽羅瓦伴隨定理、雙命名空間至統一核心編譯保持定理、Morita 等價與局部化屋頂定理；反擬陣語境半直積同態與伸縮短正合序列分裂截面定理。
3. **M8–M11 第二階段基礎定理群**：嚴格正性阻斷雙重否定悖論與巢狀稀疏參數化遮罩定理、Dybjer-Setzer 歸納-遞歸同時解碼定理、Forsberg-Kaposi 歸納-歸納互鎖良構與遞歸-遞歸消元定理；Lambek 終流奇偶同構、Rutten 流卷積導數 Leibniz 定理、餘模式字典樹精確分割、時鐘守護信用生產力與 Hopcroft-Karp 並查集無限視界雙模擬定理；四元仿射—量化半環伽羅瓦殘差、零階依賴類型形成自由、乘性張量與加性配對區隔及零階執行期抹除定理；Knuth-Bendix 遞減隱含重寫強終止與模重寫 Miller 模式合一定理、菱形相干強制轉換升降定理、64-bit Popcount $O(1)$ 結構紀錄標準形與生成式名義品牌隔離定理。
4. **M12–M14 第二階段範疇對偶與全棧總成定理群**：始代數有限觀測與終共同代數無窮流之 Chu-Galois 自對偶定理、去森林化雙變形融合定理（`hylo == cata ∘ ana`）、雙模擬局部化 $\mathsf{Coalg}[\mathsf{Bisim}^{-1}]$ 升格為 $O(1)$ Arena 整數相等定理、II 內在語法至 NbE 反射定理；隱含參數精化零執行期資源開銷定理、64-bit 結構紀錄融合推出普遍投影定理、次結構 BCKW 證明自動分層定理，以及十九概念跨階段聯合認證健全性定理。

---

## 二、資料夾內已實作之演算法列表

| 子模組資料夾 | 核心演算法族群 | 代表複雜度與硬體／位元優化 |
| :--- | :--- | :--- |
| `m1_syntax_context` | 64-bit 位元摘要 AST、Hash-Consed Arena、顯式 $\sigma$-代換、反擬陣、Operad | $O(1)$ 封閉性／變數出現／雜湊快篩 |
| `m2_universe_cumul` | 代數宇宙、Fuss-Free 小性、Tarjan SCC + SPFA 伽羅瓦求解、Ramsey 分層 | $O(1)$ 64 變數可達快篩；多項式完備蘊涵判定 |
| `m3_pi_sigma_types` | 帶類型中性項 Kripke NbE、雙向檢驗、柯里化與 Skolem 同構 | $O(1)$ 層級轉索引 `d - 1 - l` |
| `m4_curry_howard_prop` | 公式$\leftrightarrow$類型雙向同構、Squash 守衛、Gentzen 切消元、CPS、抹除提取 | 雙重良基指標保證切消元終止 |
| `m5_fibration_kan` | 劈裂重索引、$\Sigma/\Pi$ Kan 擴張、語境拉回、Beck-Chevalley、層黏合 | 線性語境偏移與 NbE 驗證 |
| `m6_chu_galois_bridge` | 64-bit Chu 空間、伽羅瓦伴隨、M4$\to$M3 編譯器、Morita、局部化、博弈 | 單指令級 `UInt64` 位元遮罩伽羅瓦運算 |
| `m7_unified_kernel` | 雙模態核心認證、半直積複合、伸縮短正合序列分裂截面 | 第一階段 7 模組閉環認證 |
| `m8_inductive_family` | 極性與巢狀嚴格正檢驗、IR 同時解碼、II 互鎖檢驗與消元、$W$-樹摺疊 | 64-bit `sp_param_mask` 與 $O(1)$ `is_leaf` |
| `m9_coalgebra_stream` | 無窮流展開、Cauchy 卷積與導數、餘模式字典樹、時鐘守護、並查集雙模擬 | $O((N_1+N_2)\alpha(N_1+N_2))$ 無限雙模擬判定 |
| `m10_affine_quant_types` | 仿射—量化半環殘差、64-bit SWAR 資源向量、雙向 QTT 檢驗、零階抹除 | 單一 `UInt64` 暫存器平行運算 32 變數重數 |
| `m11_polymorphism_coercion_nom` | 多型隱含展開、終止重寫、Miller 模式合一、相干強制轉換、結構／名義型別 | 12 指令無分支 `popcount64` $O(1)$ 稀疏結構欄位定位 |
| `m12_initial_final_duality` | 代數—共同代數 Chu 空間、去森林化 `hylo`、雙模擬商最小化駐留、II 反射 | 無限流雙模擬化約為 $O(1)$ Arena 整數比較 |
| `m13_qtt_elaboration_bridge` | 零開銷隱含$\to$QTT 編譯、64-bit 結構紀錄推出、BCKW 次結構分類 | `m1 & m2` / `m1 \| m2` $O(1)$ 紀錄欄位推出 |
| `m14_phase2_unified_system` | 十九概念全棧註冊、精化、雙模擬駐留、資源認證與全域遙測 | 跨全棧 14 模組零警告聯合運行 |

---

## 三、資料夾視角的依賴關係圖

```text
  [獨立基礎層 I-A]   m1_syntax_context   m2_universe_cumul   m3_pi_sigma_types   m4_curry_howard_prop
                            │                   │                   │                    │
                            └─────────┬─────────┴─────────┬─────────┴──────────┬─────────┘
                                      ▼                   ▼                    ▼
  [範疇融合層 II-A]           m5_fibration_kan    m6_chu_galois_bridge   m7_unified_kernel
                                      │                   │                    │
  [獨立基礎層 I-B]   m8_inductive_family  m9_coalgebra_stream  m10_affine_quant_types  m11_polymorphism_coercion_nom
                            │                   │                      │                         │
                            └─────────┬─────────┘                      └────────────┬────────────┘
                                      ▼                                             ▼
  [範疇融合層 II-B]       m12_initial_final_duality                    m13_qtt_elaboration_bridge
                                      │                                             │
                                      └──────────────────────┬──────────────────────┘
                                                             ▼
  [全棧總成核心]                               m14_phase2_unified_system
```

---

## 四、資料夾內動線及接入與輸出接口

### 內部動線
1. 八個基礎模組（`m1..m4` 與 `m8..m11`）各自零外部依賴，封裝獨立公理與常數級／多項式級核心演算法。
2. 四個中層範疇橋接模組（`m5, m6, m12, m13`）執行纖維化、Kan 擴張、Chu-Galois 對偶、雙模擬局部化與量化精化融合。
3. 兩個階段總成核心（`m7` 與頂層 `m14`）匯聚全棧認證接口。

### 接入與輸出接口
- 外部專案可引入頂層 `dtt/m14_phase2_unified_system@0.1.0` 使用全套十九概念 API，或按需單獨引入 `dtt/m1_*` 至 `dtt/m13_*` 任一子模組。
