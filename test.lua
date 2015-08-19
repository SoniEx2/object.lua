local object = require"object"

local pattern = object.pattern

local p = pattern.str("Hello") .. pattern.character(","):quantify("optional") .. pattern.character(" ") .. pattern.set("W", "w") .. pattern.str("orld!") .. pattern.presets.endwith

print(p)
print(p:match("Hello, world!"))
print(p:match("Hello world!"))
print(p:match("Hello, World!"))
print(p:match("Hello World!"))