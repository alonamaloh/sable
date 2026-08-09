const { workspace } = require("vscode");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");

let client;

function activate() {
  const serverPath = workspace.getConfiguration("sable").get("serverPath", "sable");
  client = new LanguageClient(
    "sable",
    "Sable Language Server",
    { command: serverPath, args: ["lsp"], transport: TransportKind.stdio },
    { documentSelector: [{ scheme: "file", language: "sable" }] }
  );
  client.start();
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
