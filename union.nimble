# Package

version       = "0.1.1"
author        = "Leorize"
description   = "Anonymous unions in Nim"
license       = "MIT"

# Dependencies

requires "nim >= 1.5.1"
requires "https://github.com/disruptek/balls >= 3.0.0 & < 4.0.0"

task test, "Run test suite":
  when defined(windows):
    exec "balls.cmd"
  else:
    exec "balls"
