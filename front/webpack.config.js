const path = require('path');
const { HotModuleReplacementPlugin, ProvidePlugin } = require("webpack");
const HtmlWebpackPlugin = require("html-webpack-plugin");
const ErrorOverlayPlugin = require('error-overlay-webpack-plugin');

const config = {
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
        new ProvidePlugin({
            React: 'react'
        }),
    ],
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

module.exports = (_, argv) => {
    if (argv.mode === 'development') {
        config.devtool = "inline-source-map";
        config.plugins.push(
            new HotModuleReplacementPlugin(),
            new ErrorOverlayPlugin(),
        );
    }
    if (argv.mode === 'production') {
        //...
    }
    return config;
};