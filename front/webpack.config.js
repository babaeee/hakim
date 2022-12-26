const path = require("path");
const { HotModuleReplacementPlugin, ProvidePlugin } = require("webpack");
const HtmlWebpackPlugin = require("html-webpack-plugin");
const ErrorOverlayPlugin = require("error-overlay-webpack-plugin");
const CopyPlugin = require("copy-webpack-plugin");

const config = {
  output: {
    publicPath: "/",
  },
  entry: "./src/index.tsx",
  module: {
    rules: [
      {
        test: /\.ya?ml$/i,
        use: "multi-yaml-loader",
      },
      {
        test: /\.v$/i,
        type: "asset/source",
      },
      {
        test: /\.css$/i,
        use: [
          "style-loader",
          {
            loader: "css-loader",
            options: {
              url: true,
            },
          },
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
      {
        test: /\.(gif|svg|jpg|png|eot|ttf|woff|woff2)$/,
        loader: "file-loader",
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
      React: "react",
    }),
    new CopyPlugin({
      patterns: [
        {
          from: "static",
          to: "static",
        },
      ],
    }),
  ],
  experiments: {
    topLevelAwait: true,
  },
  devServer: {
    port: 4000,
    historyApiFallback: true,
  },
};

module.exports = (_, argv) => {
  if (argv.mode === "development") {
    config.devtool = "inline-source-map";
    config.plugins.push(
      new HotModuleReplacementPlugin(),
      new ErrorOverlayPlugin()
    );
  }
  if (argv.mode === "production") {
    //...
  }
  return config;
};
