import Game.Levels.L1RealAnalysisStory
import Game.Levels.L1PsetIntro
import Game.Levels.L2NewtonsCalculationOfPi
import Game.Levels.L2PsetIntro
import Game.Levels.L3Lecture
import Game.Levels.L3PsetIntro
import Game.Levels.L4Lecture
import Game.Levels.L4PsetIntro
import Game.Levels.L5Lecture
import Game.Levels.L6Lecture
import Game.Levels.L6PsetIntro
import Game.Levels.L7Lecture
import Game.Levels.L7PsetIntro
import Game.Levels.L8Lecture
import Game.Levels.L8PsetIntro
import Game.Levels.L9Lecture
import Game.Levels.L9PsetIntro
import Game.Levels.L10Lecture
import Game.Levels.L10PsetIntro
import Game.Levels.L11Lecture
import Game.Levels.L11PsetIntro
import Game.Levels.L12Lecture
import Game.Levels.L12PsetIntro
import Game.Levels.L13Lecture
import Game.Levels.L13PsetIntro

-- exercise for later : why not `|a n - a (n + 1)|`?

Dependency NewtonsCalculationOfPi → L2Pset

Dependency NewtonsCalculationOfPi → Lecture3

Dependency L2Pset → Lecture4

Dependency Lecture4 → Lecture5

Dependency Lecture5 → Lecture6

Dependency L4Pset → Lecture6

Dependency Lecture6 → Lecture7

Dependency L6Pset → Lecture8

Dependency L9Pset → Lecture11

Dependency Lecture10 → Lecture11

Dependency Lecture11 → Lecture12

Dependency Lecture11 → L11Pset

Dependency L10Pset → Lecture12

Dependency Lecture12 → L12Pset

Dependency L11Pset → Lecture13

Dependency Lecture13 → L13Pset

-- Here's what we'll put on the title screen
Title "An Introduction to (Formal) Real Analysis"

Introduction "
# Welcome to Real Analysis, The Game!

This course is currently being developed for Rutgers University Math 311H by [Alex Kontorovich](https://math.rutgers.edu/~alexk).
 Please email alex.kontorovich@rutgers.edu for suggestions/corrections,
or better yet, post a PR/issue to
https://github.com/AlexKontorovich/RealAnalysisGame.

For the main course website, go to: https://alexkontorovich.github.io/2025F311H.

This course takes you through an Introduction to the Real Numbers, rigorous `ε`-`δ` Calculus,
and basic Point-Set Topology.
To get started, click on
**\"Level 1: The Story of Real Analysis\"**, and good luck!

"

Info "
*An Introduction to Formal Real Analysis - Interactive Edition*

## About this Course

This course follows the historical crises that forced mathematicians to rebuild
mathematics from the ground up in the 19th century. You'll learn why concepts
like `ε`-`δ` definitions became necessary and how to use them to do advanced calculus.

## Credits

* **Course Design:** By Alex Kontorovich alex.kontorovich@rutgers.edu
* **Interactive Implementation:** Lean 4 Game Engine
* **Mathematical Content:** Following Rudin, Stein-Shakarchi, Abbot, etc.
* **Many thanks to:** Jon Eugster, Heather Macbeth, Michael Stoll, and the students of 311H for a lot of technical support, encouragement, and many great suggestions for improvement!
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "A First Course in Real Analysis"
CaptionLong "Learn real analysis through the historical crises that forced mathematicians to rebuild calculus from the ground up in the 19th century."

set_option lean4game.showDependencyReasons true

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
