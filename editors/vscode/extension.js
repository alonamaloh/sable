const { workspace, window } = require("vscode");
const { LanguageClient } = require("vscode-languageclient/node");

let client;

function activate() {
  const serverPath = workspace.getConfiguration("sable").get("serverPath", "sable");
  client = new LanguageClient(
    "sable",
    "Sable Language Server",
    { command: serverPath, args: ["lsp"] },
    { documentSelector: [{ scheme: "file", language: "sable" }] }
  );
  client.start().catch((err) => {
    window.showErrorMessage(
      `Sable language server failed to start (${serverPath} lsp): ${err.message}. ` +
        `Set "sable.serverPath" to the sable binary.`
    );
  });
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
