import { g } from "../../i18n";
import css from "./Adventure.module.css";
import dataNotTyped from "../../../adventure/fa/root.yml";
import { useLocation, Link, useNavigate } from "react-router-dom";
import { setGoal } from "../../hakim";
import { AfterProofAction, openProofSession } from "../root/Root";
import { isWinNode } from "./winList";
import { Title } from "../util/Title";
import { useEffect } from "react";

export type Node = {
    id: string,
    name: string,
    x: number,
    y: number,
    dependencies?: string[] | undefined,
};

export type Level = Node & {
    type: "level",
    goal: string,
};

export type Collection = Node & {
    type: "collection",
    children: (Level | Collection)[],
};

const checkValidNode = (node: any) => {
    if (typeof node.id !== 'string') throw new Error(`Node without id: ${JSON.stringify(node)}`);
    if (typeof node.x !== 'number' || typeof node.x !== 'number') throw new Error(`Invalid position for ${node.id}`);
    if (typeof node.name !== 'string') throw new Error(`Invalid name for ${node.id}`);
};

const checkValidCollectionOrLevelArray = (array: any, parent: string) => {
    if (array instanceof Array) {
        array.forEach((x) => {
            if (typeof x.type !== 'string') {
                throw new Error(`node ${x.id} has no type`);
            }
            if (x.type === 'collection') {
                checkValidCollection(x);
            } else {
                checkValidLevel(x);
            }
        })
        return;
    }
    throw new Error(`invalid children array for ${parent}`);
};

const checkValidCollection = (node: any) => {
    checkValidNode(node);
    checkValidCollectionOrLevelArray(node.children, node.id);
};

const checkValidLevel = (node: any) => {
    checkValidNode(node);
    if (node.type !== 'level') throw new Error(`Node ${node.id} is not a level, but a ${node.type}`);
    if (typeof node.goal !== 'string') throw new Error(`Invalid goal for ${node.id}`);
};

const isLocked = (node: Node, parent: (Level | Collection)[]) => {
    if (!node.dependencies) {
        return false;
    }
    return node.dependencies.find((x) => isWinNode(parent.find((y) => y.id === x)!)) === undefined;
};

try {
    checkValidCollectionOrLevelArray(dataNotTyped, 'root');
} catch (e) {
    alert((e as any).toString());
}

const data: Collection = {
    id: 'root',
    name: '',
    type: 'collection',
    x: 0,
    y: 0,
    children: dataNotTyped as any,
};

type LockProps = {
    state: "open" | "locked" | "done",
};

const Lock: React.FC<LockProps> = ({ state }) => {
    const lock = <svg height="100%" width="100%" viewBox="0 0 309.05 400.84">
        <g id="g835" transform="translate(-99.356 -37.981)" dangerouslySetInnerHTML=
            {{
                __html: `<path id="path566" style="stroke-linejoin:round;fill-rule:evenodd;stroke:#000000;stroke-width:10;fill:#fff600" d="m159.02 181.17 261.87 0.79v194.62l-260.29 1.58-1.58-196.99z" sodipodi:nodetypes="ccccc" inkscape:connector-curvature="0" transform="translate(-17.484,55.585)" />
            <path id="path567" style="stroke-linejoin:round;fill-rule:evenodd;stroke:#000000;stroke-width:10;fill:#ffdd00" d="m159.02 180.38c-10.29-3.16-30.06-3.16-37.18-27.69v201.74s11.07 25.32 38.76 23.73c0.79-9.49-1.58-200.15-1.58-197.78z" sodipodi:nodetypes="ccccc" inkscape:connector-curvature="0" transform="translate(-17.484,55.585)" />
            <path id="path568" style="stroke-linejoin:round;fill-rule:evenodd;stroke:#000000;stroke-width:10;fill:#fff600" d="m122.63 153.48c5.8-11.87 177.74-5.54 266.61-4.75 7.91 0 28.48 11.08 31.65 32.44 0 2.37-262.66 0-262.66 0-2.37-3.95-26.9 0-35.6-27.69z" sodipodi:nodetypes="ccccc" inkscape:connector-curvature="0" transform="translate(-17.484,55.585)" />
            <path id="path569" style="stroke-linejoin:round;fill-rule:evenodd;stroke:#000000;stroke-width:10;fill:#4c4c4c" d="m142.4 180.38c0-0.79-2.37-77.53-0.79-104.43 30.86-112.34 212.03-77.532 214.4-1.583 2.38 43.513 0.79 107.59 0.79 106.8-6.33 12.66-31.64 8.7-37.18 0.79 0-9.49-0.79-50.63 0-103.64-18.99-62.497-128.96-56.168-142.4-4.744 0 53.794 0.79 109.17 0.79 109.17-4.75 7.91-29.27 14.24-35.61-2.37z" sodipodi:nodetypes="ccccccccc" inkscape:connector-curvature="0" transform="translate(10.206,38.972)" />
            <path id="path570" style="fill-rule:evenodd;stroke:#000000;stroke-width:3.75;fill:#000000" d="m214.4 411.39 103.64 0.79-35.6-90.98c15.03 2.38 40.34-59.33-15.83-65.66-57.75 7.12-37.97 63.29-18.19 67.24l-34.02 88.61z" sodipodi:nodetypes="cccccc" inkscape:connector-curvature="0" transform="translate(6.25,-3.75)" />
            <path id="path572" style="fill-rule:evenodd;fill:#ffdd00" d="m141.61 429.59s19.78-139.24 90.19-178.8c-20.56-6.33-97.31-6.33-90.19 0.79-0.79 14.24-0.79 179.59 0 178.01z" sodipodi:nodetypes="cccc" inkscape:connector-curvature="0" transform="translate(6.25,-3.75)" />
            <path id="path573" style="fill-rule:evenodd;fill:#ffdd00" d="m141.61 211.23c-11.86-0.79-31.59 0.88-36.39 2.38-2.6 9.31 15.82 18.19 27.69 21.36 29.01 4.75 56.44 3.16 84.65 2.37-22.94-1.84-63.29 1.85-68.83-5.54-6.33-4.48-11.86-13.71-7.12-20.57z" sodipodi:nodetypes="cccccc" inkscape:connector-curvature="0" transform="translate(6.25,-3.75)" />
            <path id="path574" style="fill-rule:evenodd;fill:#ffffff;fill-opacity:.75" d="m389.24 245.25s7.12 171.68-2.37 185.92c-14.24 0.79-79.91-0.79-79.91-0.79 27.69-20.57 68.04-53.01 82.28-185.13z" sodipodi:nodetypes="cccc" inkscape:connector-curvature="0" transform="translate(6.25,-3.75)" />
            <path id="path575" style="fill-rule:evenodd;fill:#ffffff;fill-opacity:.75" d="m366.3 211.23s7.91 8.71 2.37 15.04c-2.37 9.49-53.8 11.07-68.83 11.86 22.15 0.79 83.07 0 90.98-1.58 5.54-1.58-16.61-27.69-24.52-25.32z" sodipodi:nodetypes="ccccc" inkscape:connector-curvature="0" transform="translate(6.25,-3.75)" />
            <path id="path576" style="fill-rule:evenodd;fill:#ffffff;fill-opacity:.5" d="m238.13 52.215c4.75-3.956 77.93-2.912 110.22 40.365 10.05 9.97 9.25 62.48 8.45 93.34-10.28-30.06-3.95-106.02-118.67-133.7z" sodipodi:nodetypes="cccc" inkscape:connector-curvature="0" transform="translate(6.25,-3.75)" />`}}
        >
        </g>
    </svg>;
    const open = <svg height="100%" width="100%" viewBox="0 0 100 100">
        <circle r={40} cx={50} cy={50} fill={'yellow'}></circle>
    </svg>;
    const done = <svg height="100%" width="100%" viewBox="0 0 173.52 198.57">
        <g transform="translate(-36.097 -595.93)">
            <path id="path3157" style={{ fill: '#008000' }} d="m36.097 739.31 20-30c16.511 12.907 17.767 19.639 24.949 30.909 36.804-72.31 74.954-104.96 128.57-144.29-51.91 53.35-83.23 89.32-130 198.58-16.193-26.29-27.333-53.62-43.523-55.2z" />
        </g>
    </svg>;
    if (state === "locked") {
        return <div className={css.lock}>{lock}</div>;
    }
    if (state === "open") {
        return <div className={css.lock}>{open}</div>;
    }
    return <div className={css.lock}>{done}</div>;
};

export const Adventure = () => {
    const location = useLocation();
    const navigator = useNavigate();
    const path = location.pathname.split('/').filter((x) => x !== "" && x !== "adventure");
    const xt = (x: number) => x * 10 + 50;
    const yt = (x: number) => x * 17 + 20;
    let d = data.children;
    let cpath = "/adventure";
    let myname = undefined;
    let levelToRender: Level | undefined = undefined;
    let levelIs404 = false;
    let levelIsLocked = false;
    for (const p of path) {
        const x = d.find((x) => x.id === p);
        if (!x) {
            levelIs404 = true;
            break;
        }
        if (isLocked(x, d)) {
            levelIsLocked = true;
            break;
        }
        if (x.type === "level") {
            levelToRender = x;
            myname = x.name;
            break;
        }
        cpath += `/${x.id}`;
        d = x.children;
        myname = x.name;
    }
    useEffect(() => {
        if (!levelToRender) return;
        const back: AfterProofAction = {
            type: 'back',
        };
        (async () => {
            if (await setGoal(levelToRender.goal)) {
                openProofSession(navigator, {
                    onCancel: back,
                    onSolve: {
                        type: 'win',
                        level: levelToRender.id,
                        then: back,
                    },
                }, true);
            }
        })();
        // cpath is function of levelToRender
        // eslint-disable-next-line react-hooks/exhaustive-deps
    }, [levelToRender?.id]);
    if (levelIs404) return <div>404</div>;
    if (levelIsLocked) return <div>{g`this_is_locked`}</div>;
    if (levelToRender) {
        return <div>
            <Title title={[g`adventure`, myname]} />
            Wait
        </div>;
    }
    const edges = d.flatMap(
        (a) => a.dependencies?.map((bid): [[number, number], [number, number]] => {
            const b = d.find((c) => c.id === bid)!;
            return [[xt(a.x), yt(a.y)], [xt(b.x), yt(b.y)]];
        }) || []
    );
    return (
        <div className={css.main}>
            <Title title={[g`adventure`, myname]} />
            <h1 className={css.title}>{g`adventure`}</h1>
            {d.map((x) => <Link to={`${location.pathname}/${x.id}`}><button style={{
                left: `${xt(x.x) - 3}vw`,
                top: `${yt(x.y)}vh`,
            }} className={css.item}>{x.name}
                <Lock state={isWinNode(x) ? "done" : isLocked(x, d) ? "locked" : "open"} />
            </button></Link>)}
            <svg className={css.lines} viewBox="0 0 100 100" preserveAspectRatio="none">
                {edges.map(([[x1, y1], [x2, y2]]) => <line
                    stroke="black"
                    strokeWidth={1}
                    x1={x1} x2={x2} y1={y1 + 4} y2={y2 + 4} />)}
            </svg>
        </div>
    );
};
