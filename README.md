# my-package


python -m pip install --config-settings="--global-option=build_ext" `
                      --config-settings="--global-option=-IC:\Program Files\Graphviz\include" `
                      --config-settings="--global-option=-LC:\Program Files\Graphviz\lib" `
                      pygraphviz

                      

leanblueprint pdf

lake exe cache get
lake -R build
lake -R -Kenv=dev update
lake -R -Kenv=dev build
DOCGEN_SRC="github"&&lake -R -Kenv=dev build MyPackage:docs
