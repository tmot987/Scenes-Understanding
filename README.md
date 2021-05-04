This repository contains code and supporting information relating to an architecture for incremental learning of state constraints for reasoning about and guiding deep architectures in determinig stability and occlusion of objects in scenes, and for providing explanations about agents actions and beliefs. 

The file 'ASP_agent.sp' gives a CR-Prolog implementation of the robotic domain representation used in the experiments.

The file 'ASP_agent_with(out).sp' gives a CR-Prolog implementation of the robotic domain representation with 5 axioms missing for being learned using the 'axiom_learn.py' algorithm.

The algorithm 'axiom_learn.py' provides the code for tree induction and extraction of missing causal laws and executability conditions.

The file 'Lenet.py' gives the Lenet implemetation used in the experiments.

The file 'Alexnet.py' gives the Alexnet implemetation used in the experiments.

To run the Deep networks above, download the desired network code and the uncompressed dataset (available on https://drive.google.com/file/d/1aPp4FSo-irTvB3x50nP9Kwjh1WZ4bL87/view?usp=sharing) in the same folder, and execute the following line in the terminal: "python3 name_of_architecture.py number_of_training_scenes", replacing 'name_of_architecture' by Lenet or Alexnet, and the 'number_of_training_scenes' by the number of scenes you want to train your architecture (e.g., 'python3 Lenet.py 100'). The requirements for running these codes are Tensorflow (we tested for version 1.4) and OpenCV.

The 'Explanations' folder provides supporting files related to the ability of providing explanatory descriptions for the agent's actions and beliefs.
