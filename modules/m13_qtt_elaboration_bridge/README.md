# Module M13：`m13_qtt_elaboration_bridge`（零開銷隱含參數至量化核心編譯橋、結構紀錄推出融合與次結構 BCKW 證明分層）

本模組為第二階段資源與精化橋接模組，聯合 **M10（仿射與量化依賴類型論 QTT）**、**M11（依賴多型、隱含參數模式合一／重寫、強制轉換與結構／名義型別）**、**M2（代數宇宙約束圖）** 與 **M4（柯里-霍華德構造性證明）**，證明並實作「隱含參數精化零執行期資源開銷」定理、宇宙多型方案之伽羅瓦約束註冊、64-bit 位元遮罩結構紀錄融合推出（Amalgamated Pushout）與次結構邏輯 BCKW 資源自動分層器。

---

## 一、資料夾內已獲得之公理、定義、命題、引理與定理列表

1. **定理 M13.T1（隱含參數精化之零執行期資源開銷與完全抹除定理）**：將 M11 經 Miller 模式合一與重寫消解後之隱含綁定／隱含應用（`is_implicit == true`）映射至 M10 之零階重數 `GZero`，顯式綁定／應用映射至目標執行期重數 `g`，則隱含推論不消耗任何線性或仿射配額（`UsageVec64` 零增量），且經 `erase_qtt_term` 後所有推論出之隱含參數百分之百抹除。
2. **定理 M13.T2（宇宙多型方案之伽羅瓦約束嵌入可滿足性定理）**：`register_poly_scheme_universes` 為多型方案配置受單調下界保護之代數宇宙變數並由 M2 計算最小非負整數賦值。
3. **定理 M13.T3（64-bit 結構紀錄融合推出／纖維積普遍投影定理）**：對結構紀錄 $R_1(m_1), R_2(m_2)$，重疊欄位集由單指令 `m1 & m2` 決定、聯合欄位集由 `m1 | m2` 決定；欄位型別定位全程復用 M11 之全函數型別層投影 `project_structural_field_ty`；若重疊欄位存在公共強制轉換子型別，則合成之頂點紀錄 `apex` 同時具備典範限制強制轉換態射 `apex => R_1` 與 `apex => R_2`。
4. **定理 M13.T4（柯里-霍華德證明之次結構邏輯 BCKW 自動分層定理）**：`classify_substructural_proof` 將 M4 證明嵌入 M10 資源檢驗器，精確區分嚴格線性 `StrictLinearBCI`（如 $I = \lambda x.x$）、仿射 `AffineBCK`（含弱化如 $K = \lambda x y.x$）與無限制直覺主義 `UnrestrictedIntuitionistic`（含縮併如 $W_{\mathrm{diag}} = \lambda x.(x,x)$）。

---

## 二、資料夾內已實作之演算法列表

| 演算法名稱 | 所在檔案 | 時間複雜度 | 功能與硬體/數據結構優化說明 |
| :--- | :--- | :--- | :--- |
| 隱含精化項至量化 QTT 編譯器 (`compile_elab_to_qtt`) | `qtt_elaboration_bridge.mbt` | $O(\|t\|)$ | 自動將隱含通道降階為 `GZero` 並檢出未解元變數 |
| 多型宇宙變數註冊求解器 (`register_poly_scheme_universes`) | `qtt_elaboration_bridge.mbt` | $O(k + \|V\| + \|E\|)$ | 對接 M2 差分圖求解最小宇宙賦值 |
| 64-bit 結構紀錄融合推出合成器 (`amalgamate_structural_records`) | `qtt_elaboration_bridge.mbt` | 遮罩交聯 $O(1)$；欄位遍歷 $O(\mathrm{popcount})$ | 利用 `m1 & m2`、`m1 \| m2` 與 `popcount64` 合成雙邊投影強制轉換 |
| 次結構 BCKW 證明資源分類器 (`classify_substructural_proof`) | `qtt_elaboration_bridge.mbt` | 多項式於證明規模 | 依 `GOne -> GAffine -> GOmega` 晶格判定最精確次結構邏輯層級 |

---

## 三、資料夾視角的依賴關係圖

```text
  [m2_universe_cumul]  [m4_curry_howard_prop]  [m10_affine_quant_types]  [m11_polymorphism_coercion_nom]
           │                     │                        │                             │
           └─────────────────────┴────────────┬───────────┴─────────────────────────────┘
                                              ▼
                           ┌─────────────────────────────────────┐
                           │     dtt/m13_qtt_elaboration_bridge  │
                           │       qtt_elaboration_bridge.mbt    │
                           └──────────────────┬──────────────────┘
                                              │
                                              ▼
                             [ dtt/m14_phase2_unified_system ]
```

---

## 四、資料夾內動線及接入與輸出接口

### 內部資料動線
1. M11 輸出之已合一 `ElabTm` 由 `compile_elab_to_qtt` 轉為 M10 `QTerm` 進行 64-bit SWAR 資源驗證與執行期抹除。
2. `amalgamate_structural_records` 在 M11 `CoercionEnv` 下合併結構紀錄並合成左右強制轉換程式。
3. `classify_substructural_proof` 將 M4 `CHTerm` 提升至 M10 完成 BCKW 精確歸類。

### 輸出公共接口（Public API）
- **類型與錯誤**：`StructuralRecordApex`, `SubstructuralClass`, `QTTBridgeError`。
- **核心函式**：`compile_elab_to_qtt`, `register_poly_scheme_universes`, `amalgamate_structural_records`, `classify_substructural_proof`。
