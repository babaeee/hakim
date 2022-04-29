import { Helmet } from "react-helmet";
import { g } from "../../i18n";

type TitleProps = {
    title: string | (string | undefined)[],
};

export const Title: React.FC<TitleProps> = ({ title }) => {
    if (typeof title === 'string') {
        title = [title];
    }
    title = [g`babaeee_coq`, ...title].filter((x) => x !== undefined);
    return <Helmet>
        <title>{title.join(' - ')}</title>
    </Helmet>;
};
