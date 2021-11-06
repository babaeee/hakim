const path = require('path');
const { HotModuleReplacementPlugin, ProvidePlugin } = require("webpack");
const HtmlWebpackPlugin = require("html-webpack-plugin");

const config = {
    mode: "development",
    output: {
        publicPath: "/",
    },
    entry: "./src/index.tsx",
    module: {
        rules: [
            {
                test: /\.ya?ml$/i,
                type: 'json',
                use: 'yaml-loader'
            },
            {
                test: /\.css$/i,
                use: [
                    'style-loader',
                    {
                        loader: "css-loader",
                        options: {
                            url: true,
                            modules: true,
                        },
                    }
                ],
            },
            {
                test: /\.(ts|js)x?$/i,
                exclude: /node_modules/,
                use: {
                    loader: "babel-loader",
                    options: {
                        presets: [
                            "@babel/preset-env",
                            "@babel/preset-react",
                            "@babel/preset-typescript",
                        ],
                    },
                },
            },
        ],
    },
    resolve: {
        extensions: [".tsx", ".ts", ".js"],
    },
    plugins: [
        new HtmlWebpackPlugin({
            template: "src/index.html",
        }),
        new HotModuleReplacementPlugin(),
        new ProvidePlugin({
            React: 'react'
        }),
    ],
    devtool: "inline-source-map",
    experiments: {
        asyncWebAssembly: true
    },
    /*devServer: {
        static: path.join(__dirname, "build"),
        historyApiFallback: true,
        port: 4000,
        open: true,
        hot: true
    },*/
};

module.exports = config;