import matplotlib.pyplot as plt
import numpy as np
from PIL import Image

from uclid5_api import Module, bmc, conjunction, datatype, enum, record, this

m = Module("blocksworld")

# Define the block type
blocks = ["A", "B", "C", "D"]
Block, A, B, C, D = enum(*blocks)

# Define the tower type
Tower, stack, empty, top, rest, is_stack, is_empty = datatype(
    "Tower", ("stack", [("top", Block), ("rest", this())]), ("empty", [])
)

# Define the state type
towers = ["left", "center", "right"]
State, _, left, center, right = record(*zip(towers, [Tower] * len(towers)))

# Define the action type
(
    Action,
    left_to_center,
    left_to_right,
    center_to_left,
    center_to_right,
    right_to_left,
    right_to_center,
) = enum(
    "left-to-center",
    "left-to-right",
    "center-to-left",
    "center-to-right",
    "right-to-left",
    "right-to-center",
)

initial_config_left = stack(A, stack(B, stack(C, stack(D, empty()))))
initial_config_center = empty()
initial_config_right = empty()

s = m.declare_var("s", State)
a = m.declare_var("c", Action)

m.init.assign(left(s), initial_config_left)
m.init.assign(center(s), initial_config_center)
m.init.assign(right(s), initial_config_right)
m.init.havoc(a)

m.next.havoc(a)

lr_branch, lc_branch, cl_branch, cr_branch, rl_branch, rc_branch, _ = m.next.branch(
    conjunction(a == left_to_right, is_stack(left(s))),
    conjunction(a == left_to_center, is_stack(left(s))),
    conjunction(a == center_to_left, is_stack(center(s))),
    conjunction(a == center_to_right, is_stack(center(s))),
    conjunction(a == right_to_left, is_stack(right(s))),
    conjunction(a == right_to_center, is_stack(right(s))),
)

lr_branch.assign(left(s), rest(left(s)))
lr_branch.assign(right(s), stack(top(left(s)), right(s)))
lc_branch.assign(left(s), rest(left(s)))
lc_branch.assign(center(s), stack(top(left(s)), center(s)))
cl_branch.assign(center(s), rest(center(s)))
cl_branch.assign(left(s), stack(top(center(s)), left(s)))
cr_branch.assign(center(s), rest(center(s)))
cr_branch.assign(right(s), stack(top(center(s)), right(s)))
rl_branch.assign(right(s), rest(right(s)))
rl_branch.assign(left(s), stack(top(right(s)), left(s)))
rc_branch.assign(right(s), rest(right(s)))
rc_branch.assign(center(s), stack(top(right(s)), center(s)))

m.assert_invariant("negated_goal", center(s) != initial_config_left)

print(m)

model = bmc(m, 10)

steps = [v for k, v in model.items() if str(k).startswith("s")]


def tower_to_list(t):
    if t == empty():
        return []
    else:
        return tower_to_list(t.arg(1)) + [str(t.arg(0))]


CB_color_cycle = [
    "#377eb8",
    "#ff7f00",
    "#4daf4a",
    "#f781bf",
    "#a65628",
    "#984ea3",
    "#999999",
    "#e41a1c",
    "#dede00",
]


def color(block):
    if block == "A":
        return CB_color_cycle[0]
    elif block == "B":
        return CB_color_cycle[1]
    elif block == "C":
        return CB_color_cycle[2]
    elif block == "D":
        return CB_color_cycle[3]
    else:
        raise ValueError(f"Unknown block {block}")


def draw_board(s, sprime):
    left = tower_to_list(s.arg(0))
    center = tower_to_list(s.arg(1))
    right = tower_to_list(s.arg(2))
    left_prime = tower_to_list(sprime.arg(0))
    center_prime = tower_to_list(sprime.arg(1))
    right_prime = tower_to_list(sprime.arg(2))

    # make a stacked bar chart in matplotlib where each tower is a bar
    # and each block is a color
    fig, ax = plt.subplots()
    # make the dimensions of the plot square
    fig.set_size_inches(len(towers), len(blocks))
    bottom = np.zeros(len(towers))
    width = 1

    for i, tower in enumerate([left, center, right]):
        for _, block in enumerate(tower):
            plt.bar(
                i,
                height=1,
                bottom=bottom[i],
                color=color(block),
                width=width,
                align="center",
                edgecolor="black",
                linewidth=2,
                alpha=0.1,
            )
            ax.text(
                i,
                bottom[i] + width / 2,
                block,
                horizontalalignment="center",
                verticalalignment="center",
                fontsize=30,
                alpha=0.1,
            )
            bottom[i] += 1

    bottom = np.zeros(len(towers))
    for i, tower in enumerate([left_prime, center_prime, right_prime]):
        for _, block in enumerate(tower):
            plt.bar(
                i,
                height=1,
                bottom=bottom[i],
                color=color(block),
                width=1,
                align="center",
                edgecolor="black",
                linewidth=2,
                alpha=1,
            )
            # add a label to the center of the block
            ax.text(
                i,
                bottom[i] + width / 2,
                block,
                horizontalalignment="center",
                verticalalignment="center",
                fontsize=30,
            )
            bottom[i] += 1

    left_add = [block for block in left_prime if block not in left]
    left_remove = [block for block in left if block not in left_prime]
    center_add = [block for block in center_prime if block not in center]
    center_remove = [block for block in center if block not in center_prime]
    right_add = [block for block in right_prime if block not in right]
    right_remove = [block for block in right if block not in right_prime]

    # find the block that moved
    if len(left_add) == 1:
        to_tower = 0
    elif len(center_add) == 1:
        to_tower = 1
    elif len(right_add) == 1:
        to_tower = 2
    else:
        to_tower = None

    if len(left_remove) == 1:
        from_tower = 0
    elif len(center_remove) == 1:
        from_tower = 1
    elif len(right_remove) == 1:
        from_tower = 2
    else:
        from_tower = None

    if to_tower is not None and from_tower is not None:
        # draw an arrow from the top of the old from_tower
        # to the top of the new to_tower
        source = (from_tower, len([left, center, right][from_tower]))
        dest = (to_tower, len([left_prime, center_prime, right_prime][to_tower]))
        fraction = (
            0.8
            / np.linalg.norm(np.array(dest) - np.array(source))
            / np.linalg.norm(np.array([2, 3]) - np.array([0, 3]))
        )

        if dest[0] > source[0]:
            ax.annotate(
                "",
                xy=(source[0], source[1]),
                xycoords="data",
                xytext=(dest[0], dest[1]),
                textcoords="data",
                arrowprops=dict(
                    arrowstyle="-",
                    color="0.5",
                    linestyle="dotted",
                    linewidth=2,
                    shrinkA=10,
                    shrinkB=10,
                    patchA=None,
                    patchB=None,
                    connectionstyle=f"bar,angle=180,fraction={fraction}",
                ),
            )
        else:
            ax.annotate(
                "",
                xy=(dest[0], dest[1]),
                xycoords="data",
                xytext=(source[0], source[1]),
                textcoords="data",
                arrowprops=dict(
                    arrowstyle="-",
                    color="0.5",
                    linestyle="dotted",
                    linewidth=2,
                    shrinkA=10,
                    shrinkB=10,
                    patchA=None,
                    patchB=None,
                    connectionstyle=f"bar,angle=180,fraction={fraction}",
                ),
            )

        # add a solid arrow of length 0 pointing to the top of the new target tower
        ax.annotate(
            "",
            xy=(dest[0], dest[1]),
            xycoords="data",
            xytext=(dest[0], dest[1] + 0.2),
            textcoords="data",
            arrowprops=dict(
                arrowstyle="-|>,head_length=0.4,head_width=0.4",
                color="0.5",
                linestyle="solid",
                linewidth=1,
                shrinkA=3,
                shrinkB=3,
                patchA=None,
                patchB=None,
                connectionstyle="arc3,rad=0",
            ),
        )
        # add a ball at the top of the old source tower
        ax.add_patch(plt.Circle((source[0], source[1] + 0.15), 0.05, color="0.5"))

    ax.set_xticks([0, 1, 2])
    ax.set_xticklabels(["left", "center", "right"])
    ax.set_yticks([])
    ax.set_ylim(-0.05, len(blocks) + width / 6 + 0.05)
    ax.set_xlim(-width / 2 - 0.05, len(towers) - width / 2 + 0.05)
    ax.set_aspect("equal")
    # remove the frame
    for spine in ax.spines.values():
        spine.set_visible(False)

    return fig


fs = []
for i in range(len(steps) - 1):
    f = draw_board(steps[i], steps[i + 1])
    fs.append(f)

fs.append(draw_board(steps[0], steps[-1]))

for i, f in enumerate(fs):
    f.savefig(f"blocksworld_{i}.png", dpi=300)

# make a gif
images = []
for i in range(len(steps)):
    images.append(Image.open(f"blocksworld_{i}.png"))

images[0].save(
    "blocksworld.gif",
    save_all=True,
    append_images=images[1:],
    optimize=False,
    duration=750,
    loop=0,
)
