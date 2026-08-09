# Editor setup

The compiler ships a language server: `sable lsp` (stdio). It provides:

- **diagnostics** — the fast front-end pass on every keystroke; the full
  Lean verification on open and save
- **hover** on a function name — its contract (`pre`/`post`/`variant`),
  never the body: the design's "no reader may be shown a function
  without its contract"
- **folding** for proof blocks
- **semantic tokens** — evidence lines are dimmed (comment-colored),
  interface lines (`pre`/`post`) are highlighted: "a reader may ignore
  proofs"

Build it once: `cd compiler && cargo build --release` (binary at
`compiler/target/release/sable`).

Optional but recommended: run `sable daemon` in a spare terminal — a
persistent Lean server that makes every check (including the LSP's
on-save verification and the Claude Code hook) ~10× faster
(~0.25s instead of ~2.4s). Everything silently falls back to the batch
path when the daemon isn't running.

## Neovim (zero plugins)

```lua
-- in init.lua
vim.filetype.add({ extension = { sable = "sable" } })

vim.api.nvim_create_autocmd("FileType", {
  pattern = "sable",
  callback = function()
    vim.lsp.start({
      name = "sable",
      cmd = { "/path/to/sable/compiler/target/release/sable", "lsp" },
    })
    vim.lsp.semantic_tokens and nil -- semantic tokens are on by default in 0.9+
  end,
})
```

## VS Code

A minimal client extension lives in `editors/vscode/`:

```sh
cd editors/vscode
npm install
npm run package        # or: open the folder in VS Code and press F5
code --install-extension sable-*.vsix
```

Set `sable.serverPath` in settings if the binary is not on your PATH.
