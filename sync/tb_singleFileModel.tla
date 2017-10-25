----------------- MODULE tb_singleFileModel -----------------
EXTENDS TLC, Naturals, singleFileModel
Spec == /\ Edit(Create(Delete(Create(Delete(Edit(Edit(Create(
               <<>>, 1, 0), 2, 1), 4, 0), 5, 2), 6, 0), 19, 0), 22, 0), 23, 0)
           = << << <<1, 0, "create">>,
                   <<2, 1, "edit">>,
                   <<4, 0, "edit">>,
                   <<5, 2, "delete">>,
                   <<6, 0, "create">>,
                   <<19, 0, "delete">>,
                   <<22, 0, "create">>,
                   <<23, 0, "edit">> >>,
                "alive" >>
        /\ Merge(Edit(Edit(Edit(Create(<<>>, 1, 0), 2, 0), 4, 0), 6, 0),
                 10,
                 0,
                 Edit(Edit(Edit(Edit(Create(<<>>, 1, 1), 3, 1), 4, 1), 8, 1), 9, 1),
                 1)
           = << << <<1, 0, "create">>,
                   <<1, 1, "create">>,
                   <<2, 0, "edit">>,
                   <<3, 1, "edit">>,
                   <<4, 0, "edit">>,
                   <<4, 1, "edit">>,
                   <<6, 0, "edit">>,
                   <<8, 1, "edit">>,
                   <<9, 1, "edit">>,
                   <<10,0, "merge", 1>> >>,
                "alive" >>
=============================================================
