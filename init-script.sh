if ! command -v wasm-pack &> /dev/null
then
    echo "installing rust..."
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
else
    echo "✓ rust exists"
fi
if ! command -v wasm-pack &> /dev/null
then
    echo "installing wasm-pack..."
    cargo install wasm-pack
    exit
else
    echo "✓ wasm-pack exists"
fi

rustup target add wasm32-unknown-unknown
rustup target add wasm32-unknown-emscripten

cd hakim-json
echo "building hakim json..."
EMCC_CFLAGS="-s TOTAL_STACK=32MB" cargo build -vv --release --target wasm32-unknown-emscripten
cd ..
node scripts/patch-emscripten.js ./target/wasm32-unknown-emscripten/release/hakim-json.js
cp ./target/wasm32-unknown-emscripten/release/hakim-json.js ./front/static/.
cp ./target/wasm32-unknown-emscripten/release/hakim_json.wasm ./front/static/.
