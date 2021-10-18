const path = require("path");
const HtmlWebPackPlugin = require("html-webpack-plugin");

module.exports = {
    mode: "development",
    entry: {
        app: "./index.js",
    },
    experiments: {
        asyncWebAssembly: true
    },
    output: {
        globalObject: "self",
        filename: "[name].bundle.js",
        path: path.resolve(__dirname, "dist"),
    },
    module: {
        rules: [
            {
                test: /\.css$/,
                use: ["style-loader", "css-loader"],
            },
            {
                test: /\.rs$/,
                use: ['raw-loader'],
            },
            {
                test: /\.ttf$/,
                use: ['file-loader']
            }
        ],
    },
    plugins: [
        new HtmlWebPackPlugin({
            title: "Rust Analyzer Playground",
            chunks: ["app"],
        }),
    ],
};
