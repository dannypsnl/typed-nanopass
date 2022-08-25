# typed-nanopass

[![Test](https://github.com/racket-tw/typed-nanopass/actions/workflows/racket-test.yml/badge.svg)](https://github.com/racket-tw/typed-nanopass/actions/workflows/racket-test.yml)
[![Coverage](https://badgen.net/https/racket-tw.github.io/typed-nanopass/coverage/badge.json)](https://racket-tw.github.io/typed-nanopass/coverage)

### Explaination

nanopass 的重點是根據語言定義自動生成走訪結構，typed 版的構想是因為我發現 nanopass 有幾個問題

1. 一個 `(a b c ...)` 之類的東西，`a` 到底是不是一個語法結構，取決於它是否是一個 meta variable。然而任何大規模的語言都會可能意外的覆蓋掉定義。我希望直接改成 `(a ,b ,c)`，讓 `,x` 表示 `x` 是一個 meta variable
2. 在編譯到 asm-like 的模型的語言時，遞迴之後要展開兩次是非常合理的。nanopass 因為只允許目前範圍內的 splicing 而變得很麻煩。我希望可以直接寫 `,@pattern`
3. 語言總是只能從 entry 進入(無論是自動生成的 parse 或是 pass 預設的進入點)，但這個限制似乎沒有什麼意義

並非核心要求的則有

- 允許為 parametric polymorphism 生成語言
- 自動平行化編譯，換句話說，由我們提供 compose 函數，而不採用內建的組合函數。盡可能的分析出可以平行化執行的程式
- 語言可以附加上型別檢查機制
- 統一的錯誤提交器
- mangling 機制
- 處理 syntax 輸入：備註這個可能沒用處，因為可能我們直接 expose surface syntax 的 ast 給 parser 就好了
