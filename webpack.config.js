const path = require("path")
module.exports = {
    entry: {
        bundle: [
            "./public/build/babel/app.js",
            "./public/build/babel/storage.js",
            "./public/build/babel/categoryView.js",
            "./public/build/babel/productView.js",
        ],
        privacy: "./public/build/babel/privacyPage.js",
    },
    output: {
        path: path.resolve(__dirname, "public/build/webpack"),
        filename: "[name].js"
    },
    module: {
        rules: [{
                test: /\.m?js$/,
                exclude: /node_modules/,
                loader: 'babel-loader',
                options: {
                    presets: ['@babel/preset-env']
            }
        },
        {
            test: /\.css$/i,
            use: ["style-loader", "css-loader"],
          },]
    }
}
