# my-package


python -m pip install --config-settings="--global-option=build_ext" `
                      --config-settings="--global-option=-IC:\Program Files\Graphviz\include" `
                      --config-settings="--global-option=-LC:\Program Files\Graphviz\lib" `
                      pygraphviz

                      

leanblueprint pdf

lake -R -Kenv=dev update
DOCGEN_SRC="github"&&lake -R -Kenv=dev build MyPackage.Basic:docs