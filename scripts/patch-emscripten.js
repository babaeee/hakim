import { readFile, writeFile } from "fs/promises";

let text = await readFile(process.argv[2]);
text += `
globalThis.hakimQueryLoad = new Promise((res) => {
    globalThis.hakimQueryCallback = res;
});
`;

text = text.replace(
  "if(shouldRunNow)callMain(args);",
  `globalThis.hakimQuery = (x) => {
const resp = UTF8ToString(
    Module._exec_command(allocateUTF8OnStack(JSON.stringify(x)))
);
return JSON.parse(resp);
};

globalThis.hakimQueryCallback();
`
);

await writeFile(process.argv[2], text);
